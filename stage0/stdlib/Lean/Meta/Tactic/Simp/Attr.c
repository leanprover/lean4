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
lean_object* l_Lean_registerAutomationAttr(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__3;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__4;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2(lean_object*);
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
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__6;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__7;
static const lean_string_object l_Lean_Meta_mkSimpAttr___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Cannot add `simp` attribute to `"};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__9;
static const lean_string_object l_Lean_Meta_mkSimpAttr___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`: It is not a proposition nor a definition (to unfold)"};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__11;
static const lean_string_object l_Lean_Meta_mkSimpAttr___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 165, .m_capacity = 165, .m_length = 164, .m_data = "The `[simp]` attribute can be added to lemmas that should be automatically used by the simplifier and to definitions that the simplifier should automatically unfold"};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__12 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__12_value;
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3_spec__4(lean_object* v_msgData_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v___x_21_; lean_object* v_env_22_; uint8_t v___x_23_; lean_object* v_env_24_; lean_object* v___x_25_; lean_object* v_toCold_26_; lean_object* v_mctx_27_; lean_object* v_lctx_28_; lean_object* v_options_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_21_ = lean_st_ref_get(v___y_19_);
v_env_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc_ref(v_env_22_);
lean_dec(v___x_21_);
v___x_23_ = 0;
v_env_24_ = l_Lean_Environment_setRecordingDeps(v_env_22_, v___x_23_);
v___x_25_ = lean_st_ref_get(v___y_17_);
v_toCold_26_ = lean_ctor_get(v___y_18_, 0);
v_mctx_27_ = lean_ctor_get(v___x_25_, 0);
lean_inc_ref(v_mctx_27_);
lean_dec(v___x_25_);
v_lctx_28_ = lean_ctor_get(v___y_16_, 2);
v_options_29_ = lean_ctor_get(v_toCold_26_, 2);
lean_inc_ref(v_options_29_);
lean_inc_ref(v_lctx_28_);
v___x_30_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_30_, 0, v_env_24_);
lean_ctor_set(v___x_30_, 1, v_mctx_27_);
lean_ctor_set(v___x_30_, 2, v_lctx_28_);
lean_ctor_set(v___x_30_, 3, v_options_29_);
v___x_31_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
lean_ctor_set(v___x_31_, 1, v_msgData_15_);
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3_spec__4___boxed(lean_object* v_msgData_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3_spec__4(v_msgData_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(lean_object* v_msg_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_ref_46_; lean_object* v___x_47_; lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_56_; 
v_ref_46_ = lean_ctor_get(v___y_43_, 2);
v___x_47_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3_spec__4(v_msg_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
v_a_48_ = lean_ctor_get(v___x_47_, 0);
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_56_ == 0)
{
v___x_50_ = v___x_47_;
v_isShared_51_ = v_isSharedCheck_56_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_a_48_);
lean_dec(v___x_47_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_56_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_52_; lean_object* v___x_54_; 
lean_inc(v_ref_46_);
v___x_52_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_52_, 0, v_ref_46_);
lean_ctor_set(v___x_52_, 1, v_a_48_);
if (v_isShared_51_ == 0)
{
lean_ctor_set_tag(v___x_50_, 1);
lean_ctor_set(v___x_50_, 0, v___x_52_);
v___x_54_ = v___x_50_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg___boxed(lean_object* v_msg_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(v_msg_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
return v_res_63_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_64_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__0);
v___x_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg(){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__1);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v___dummy_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg();
return v_res_70_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__0);
v___x_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0);
v___x_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
return v___x_74_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg();
return v___x_75_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0);
v___x_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
return v___x_77_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_78_ = lean_unsigned_to_nat(0u);
v___x_79_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0);
v___x_80_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
lean_ctor_set(v___x_80_, 2, v___x_78_);
return v___x_80_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_81_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__4, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__4_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__4);
v___x_82_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__3);
v___x_83_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__0);
v___x_84_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2);
v___x_85_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v___x_83_);
lean_ctor_set(v___x_85_, 2, v___x_82_);
lean_ctor_set(v___x_85_, 3, v___x_83_);
lean_ctor_set(v___x_85_, 4, v___x_83_);
lean_ctor_set(v___x_85_, 5, v___x_83_);
lean_ctor_set(v___x_85_, 6, v___x_83_);
lean_ctor_set(v___x_85_, 7, v___x_81_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(lean_object* v_ext_86_, lean_object* v_b_87_, uint8_t v_kind_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_toCold_93_; lean_object* v_currNamespace_94_; lean_object* v___x_95_; lean_object* v_env_96_; lean_object* v_nextMacroScope_97_; lean_object* v_ngen_98_; lean_object* v_auxDeclNGen_99_; lean_object* v_traceState_100_; lean_object* v_recordedDeps_101_; lean_object* v_messages_102_; lean_object* v_infoState_103_; lean_object* v_snapshotTasks_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_131_; 
v_toCold_93_ = lean_ctor_get(v___y_90_, 0);
v_currNamespace_94_ = lean_ctor_get(v_toCold_93_, 4);
v___x_95_ = lean_st_ref_take(v___y_91_);
v_env_96_ = lean_ctor_get(v___x_95_, 0);
v_nextMacroScope_97_ = lean_ctor_get(v___x_95_, 1);
v_ngen_98_ = lean_ctor_get(v___x_95_, 2);
v_auxDeclNGen_99_ = lean_ctor_get(v___x_95_, 3);
v_traceState_100_ = lean_ctor_get(v___x_95_, 4);
v_recordedDeps_101_ = lean_ctor_get(v___x_95_, 6);
v_messages_102_ = lean_ctor_get(v___x_95_, 7);
v_infoState_103_ = lean_ctor_get(v___x_95_, 8);
v_snapshotTasks_104_ = lean_ctor_get(v___x_95_, 9);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_131_ == 0)
{
lean_object* v_unused_132_; 
v_unused_132_ = lean_ctor_get(v___x_95_, 5);
lean_dec(v_unused_132_);
v___x_106_ = v___x_95_;
v_isShared_107_ = v_isSharedCheck_131_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_snapshotTasks_104_);
lean_inc(v_infoState_103_);
lean_inc(v_messages_102_);
lean_inc(v_recordedDeps_101_);
lean_inc(v_traceState_100_);
lean_inc(v_auxDeclNGen_99_);
lean_inc(v_ngen_98_);
lean_inc(v_nextMacroScope_97_);
lean_inc(v_env_96_);
lean_dec(v___x_95_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_131_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_111_; 
lean_inc(v_currNamespace_94_);
v___x_108_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_96_, v_ext_86_, v_b_87_, v_kind_88_, v_currNamespace_94_);
v___x_109_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 5, v___x_109_);
lean_ctor_set(v___x_106_, 0, v___x_108_);
v___x_111_ = v___x_106_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_nextMacroScope_97_);
lean_ctor_set(v_reuseFailAlloc_130_, 2, v_ngen_98_);
lean_ctor_set(v_reuseFailAlloc_130_, 3, v_auxDeclNGen_99_);
lean_ctor_set(v_reuseFailAlloc_130_, 4, v_traceState_100_);
lean_ctor_set(v_reuseFailAlloc_130_, 5, v___x_109_);
lean_ctor_set(v_reuseFailAlloc_130_, 6, v_recordedDeps_101_);
lean_ctor_set(v_reuseFailAlloc_130_, 7, v_messages_102_);
lean_ctor_set(v_reuseFailAlloc_130_, 8, v_infoState_103_);
lean_ctor_set(v_reuseFailAlloc_130_, 9, v_snapshotTasks_104_);
v___x_111_ = v_reuseFailAlloc_130_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v_mctx_114_; lean_object* v_zetaDeltaFVarIds_115_; lean_object* v_postponed_116_; lean_object* v_diag_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_128_; 
v___x_112_ = lean_st_ref_put(v___y_91_, v___x_111_);
v___x_113_ = lean_st_ref_take(v___y_89_);
v_mctx_114_ = lean_ctor_get(v___x_113_, 0);
v_zetaDeltaFVarIds_115_ = lean_ctor_get(v___x_113_, 2);
v_postponed_116_ = lean_ctor_get(v___x_113_, 3);
v_diag_117_ = lean_ctor_get(v___x_113_, 4);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_128_ == 0)
{
lean_object* v_unused_129_; 
v_unused_129_ = lean_ctor_get(v___x_113_, 1);
lean_dec(v_unused_129_);
v___x_119_ = v___x_113_;
v_isShared_120_ = v_isSharedCheck_128_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_diag_117_);
lean_inc(v_postponed_116_);
lean_inc(v_zetaDeltaFVarIds_115_);
lean_inc(v_mctx_114_);
lean_dec(v___x_113_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_128_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_121_ = lean_box(0);
v___x_122_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__5, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__5_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__5);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 1, v___x_122_);
v___x_124_ = v___x_119_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_mctx_114_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_127_, 2, v_zetaDeltaFVarIds_115_);
lean_ctor_set(v_reuseFailAlloc_127_, 3, v_postponed_116_);
lean_ctor_set(v_reuseFailAlloc_127_, 4, v_diag_117_);
v___x_124_ = v_reuseFailAlloc_127_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_st_ref_put(v___y_89_, v___x_124_);
v___x_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_121_);
return v___x_126_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___boxed(lean_object* v_ext_133_, lean_object* v_b_134_, lean_object* v_kind_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
uint8_t v_kind_boxed_140_; lean_object* v_res_141_; 
v_kind_boxed_140_ = lean_unbox(v_kind_135_);
v_res_141_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(v_ext_133_, v_b_134_, v_kind_boxed_140_, v___y_136_, v___y_137_, v___y_138_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addDeclToUnfold_spec__1(lean_object* v_ext_142_, uint8_t v_post_143_, uint8_t v_a_144_, uint8_t v_attrKind_145_, lean_object* v_prio_146_, lean_object* v_as_147_, size_t v_sz_148_, size_t v_i_149_, lean_object* v_b_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
uint8_t v___x_156_; 
v___x_156_ = lean_usize_dec_lt(v_i_149_, v_sz_148_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; 
lean_dec(v_prio_146_);
lean_dec_ref(v_ext_142_);
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v_b_150_);
return v___x_157_;
}
else
{
lean_object* v___x_158_; lean_object* v_a_159_; lean_object* v___x_160_; 
v___x_158_ = lean_box(0);
v_a_159_ = lean_array_uget_borrowed(v_as_147_, v_i_149_);
lean_inc(v_prio_146_);
lean_inc(v_a_159_);
lean_inc_ref(v_ext_142_);
v___x_160_ = l_Lean_Meta_addSimpTheorem(v_ext_142_, v_a_159_, v_post_143_, v_a_144_, v_attrKind_145_, v_prio_146_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
if (lean_obj_tag(v___x_160_) == 0)
{
size_t v___x_161_; size_t v___x_162_; 
lean_dec_ref_known(v___x_160_, 1);
v___x_161_ = ((size_t)1ULL);
v___x_162_ = lean_usize_add(v_i_149_, v___x_161_);
v_i_149_ = v___x_162_;
v_b_150_ = v___x_158_;
goto _start;
}
else
{
lean_dec(v_prio_146_);
lean_dec_ref(v_ext_142_);
return v___x_160_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addDeclToUnfold_spec__1___boxed(lean_object* v_ext_164_, lean_object* v_post_165_, lean_object* v_a_166_, lean_object* v_attrKind_167_, lean_object* v_prio_168_, lean_object* v_as_169_, lean_object* v_sz_170_, lean_object* v_i_171_, lean_object* v_b_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
uint8_t v_post_boxed_178_; uint8_t v_a_4024__boxed_179_; uint8_t v_attrKind_boxed_180_; size_t v_sz_boxed_181_; size_t v_i_boxed_182_; lean_object* v_res_183_; 
v_post_boxed_178_ = lean_unbox(v_post_165_);
v_a_4024__boxed_179_ = lean_unbox(v_a_166_);
v_attrKind_boxed_180_ = lean_unbox(v_attrKind_167_);
v_sz_boxed_181_ = lean_unbox_usize(v_sz_170_);
lean_dec(v_sz_170_);
v_i_boxed_182_ = lean_unbox_usize(v_i_171_);
lean_dec(v_i_171_);
v_res_183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addDeclToUnfold_spec__1(v_ext_164_, v_post_boxed_178_, v_a_4024__boxed_179_, v_attrKind_boxed_180_, v_prio_168_, v_as_169_, v_sz_boxed_181_, v_i_boxed_182_, v_b_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec_ref(v_as_169_);
return v_res_183_;
}
}
static lean_object* _init_l_Lean_Meta_addDeclToUnfold___closed__2(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = ((lean_object*)(l_Lean_Meta_addDeclToUnfold___closed__1));
v___x_189_ = l_Lean_stringToMessageData(v___x_188_);
return v___x_189_;
}
}
static lean_object* _init_l_Lean_Meta_addDeclToUnfold___closed__4(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = ((lean_object*)(l_Lean_Meta_addDeclToUnfold___closed__3));
v___x_192_ = l_Lean_stringToMessageData(v___x_191_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_Meta_addDeclToUnfold___closed__6(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = ((lean_object*)(l_Lean_Meta_addDeclToUnfold___closed__5));
v___x_195_ = l_Lean_stringToMessageData(v___x_194_);
return v___x_195_;
}
}
static lean_object* _init_l_Lean_Meta_addDeclToUnfold___closed__7(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = lean_obj_once(&l_Lean_Meta_addDeclToUnfold___closed__6, &l_Lean_Meta_addDeclToUnfold___closed__6_once, _init_l_Lean_Meta_addDeclToUnfold___closed__6);
v___x_197_ = l_Lean_MessageData_note(v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDeclToUnfold(lean_object* v_ext_198_, lean_object* v_declName_199_, uint8_t v_post_200_, uint8_t v_inv_201_, lean_object* v_prio_202_, uint8_t v_attrKind_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v___x_209_; lean_object* v_env_210_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_218_; 
v___x_209_ = lean_st_ref_get(v_a_207_);
v_env_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc_ref(v_env_210_);
lean_dec(v___x_209_);
lean_inc(v_declName_199_);
v___x_211_ = l_Lean_getOriginalConstKind_x3f(v_env_210_, v_declName_199_);
v___x_212_ = ((lean_object*)(l_Lean_Meta_addDeclToUnfold___closed__0));
v___x_213_ = l_instBEqOption_beq___at___00Lean_Meta_addDeclToUnfold_spec__0(v___x_211_, v___x_212_);
lean_dec(v___x_211_);
if (v___x_213_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; 
lean_dec(v_prio_202_);
lean_dec(v_declName_199_);
lean_dec_ref(v_ext_198_);
v___x_307_ = lean_box(v___x_213_);
v___x_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
return v___x_308_;
}
else
{
if (v_inv_201_ == 0)
{
v___y_215_ = v_a_204_;
v___y_216_ = v_a_205_;
v___y_217_ = v_a_206_;
v___y_218_ = v_a_207_;
goto v___jp_214_;
}
else
{
lean_object* v___x_309_; uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
lean_dec(v_prio_202_);
lean_dec_ref(v_ext_198_);
v___x_309_ = lean_obj_once(&l_Lean_Meta_addDeclToUnfold___closed__2, &l_Lean_Meta_addDeclToUnfold___closed__2_once, _init_l_Lean_Meta_addDeclToUnfold___closed__2);
v___x_310_ = 0;
v___x_311_ = l_Lean_MessageData_ofConstName(v_declName_199_, v___x_310_);
v___x_312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_309_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = lean_obj_once(&l_Lean_Meta_addDeclToUnfold___closed__4, &l_Lean_Meta_addDeclToUnfold___closed__4_once, _init_l_Lean_Meta_addDeclToUnfold___closed__4);
v___x_314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_312_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = lean_obj_once(&l_Lean_Meta_addDeclToUnfold___closed__7, &l_Lean_Meta_addDeclToUnfold___closed__7_once, _init_l_Lean_Meta_addDeclToUnfold___closed__7);
v___x_316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(v___x_316_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
v_a_318_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_317_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_317_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
v___jp_214_:
{
lean_object* v___x_219_; 
lean_inc(v_declName_199_);
v___x_219_ = l_Lean_Meta_Simp_ignoreEquations(v_declName_199_, v___y_217_, v___y_218_);
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_306_; 
v_a_220_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_306_ == 0)
{
v___x_222_ = v___x_219_;
v_isShared_223_ = v_isSharedCheck_306_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_219_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_306_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
uint8_t v___x_224_; 
v___x_224_ = lean_unbox(v_a_220_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; 
lean_inc(v_declName_199_);
v___x_225_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_199_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_226_);
lean_dec_ref_known(v___x_225_, 1);
if (lean_obj_tag(v_a_226_) == 1)
{
lean_object* v_val_227_; lean_object* v___x_228_; size_t v_sz_229_; size_t v___x_230_; uint8_t v___x_231_; lean_object* v___x_232_; 
lean_del_object(v___x_222_);
v_val_227_ = lean_ctor_get(v_a_226_, 0);
lean_inc(v_val_227_);
lean_dec_ref_known(v_a_226_, 1);
v___x_228_ = lean_box(0);
v_sz_229_ = lean_array_size(v_val_227_);
v___x_230_ = ((size_t)0ULL);
v___x_231_ = lean_unbox(v_a_220_);
lean_dec(v_a_220_);
lean_inc_ref(v_ext_198_);
v___x_232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addDeclToUnfold_spec__1(v_ext_198_, v_post_200_, v___x_231_, v_attrKind_203_, v_prio_202_, v_val_227_, v_sz_229_, v___x_230_, v___x_228_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_262_; 
lean_dec_ref_known(v___x_232_, 1);
lean_inc(v_declName_199_);
v___x_233_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_233_, 0, v_declName_199_);
lean_ctor_set(v___x_233_, 1, v_val_227_);
lean_inc_ref(v_ext_198_);
v___x_234_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(v_ext_198_, v___x_233_, v_attrKind_203_, v___y_216_, v___y_217_, v___y_218_);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_262_ == 0)
{
lean_object* v_unused_263_; 
v_unused_263_ = lean_ctor_get(v___x_234_, 0);
lean_dec(v_unused_263_);
v___x_236_ = v___x_234_;
v_isShared_237_ = v_isSharedCheck_262_;
goto v_resetjp_235_;
}
else
{
lean_dec(v___x_234_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_262_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_238_; 
lean_inc(v_declName_199_);
v___x_238_ = l_Lean_Meta_Simp_unfoldEvenWithEqns___redArg(v_declName_199_, v___y_218_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_261_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_261_ == 0)
{
v___x_241_ = v___x_238_;
v_isShared_242_ = v_isSharedCheck_261_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_238_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_261_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
uint8_t v___x_243_; 
v___x_243_ = lean_unbox(v_a_239_);
lean_dec(v_a_239_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_246_; 
lean_del_object(v___x_236_);
lean_dec(v_declName_199_);
lean_dec_ref(v_ext_198_);
v___x_244_ = lean_box(v___x_213_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 0, v___x_244_);
v___x_246_ = v___x_241_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
else
{
lean_object* v___x_249_; 
lean_del_object(v___x_241_);
if (v_isShared_237_ == 0)
{
lean_ctor_set_tag(v___x_236_, 1);
lean_ctor_set(v___x_236_, 0, v_declName_199_);
v___x_249_ = v___x_236_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_declName_199_);
v___x_249_ = v_reuseFailAlloc_260_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_258_; 
v___x_250_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(v_ext_198_, v___x_249_, v_attrKind_203_, v___y_216_, v___y_217_, v___y_218_);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_258_ == 0)
{
lean_object* v_unused_259_; 
v_unused_259_ = lean_ctor_get(v___x_250_, 0);
lean_dec(v_unused_259_);
v___x_252_ = v___x_250_;
v_isShared_253_ = v_isSharedCheck_258_;
goto v_resetjp_251_;
}
else
{
lean_dec(v___x_250_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_258_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_254_ = lean_box(v___x_213_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v___x_254_);
v___x_256_ = v___x_252_;
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
}
}
}
}
else
{
lean_del_object(v___x_236_);
lean_dec(v_declName_199_);
lean_dec_ref(v_ext_198_);
return v___x_238_;
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
lean_dec(v_val_227_);
lean_dec(v_declName_199_);
lean_dec_ref(v_ext_198_);
v_a_264_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_232_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_232_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
else
{
lean_object* v___x_273_; 
lean_dec(v_a_226_);
lean_dec(v_a_220_);
lean_dec(v_prio_202_);
if (v_isShared_223_ == 0)
{
lean_ctor_set_tag(v___x_222_, 1);
lean_ctor_set(v___x_222_, 0, v_declName_199_);
v___x_273_ = v___x_222_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_declName_199_);
v___x_273_ = v_reuseFailAlloc_284_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
lean_object* v___x_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_282_; 
v___x_274_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(v_ext_198_, v___x_273_, v_attrKind_203_, v___y_216_, v___y_217_, v___y_218_);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_282_ == 0)
{
lean_object* v_unused_283_; 
v_unused_283_ = lean_ctor_get(v___x_274_, 0);
lean_dec(v_unused_283_);
v___x_276_ = v___x_274_;
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
else
{
lean_dec(v___x_274_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_278_ = lean_box(v___x_213_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_278_);
v___x_280_ = v___x_276_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
else
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
lean_del_object(v___x_222_);
lean_dec(v_a_220_);
lean_dec(v_prio_202_);
lean_dec(v_declName_199_);
lean_dec_ref(v_ext_198_);
v_a_285_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_225_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_225_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
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
else
{
lean_object* v___x_294_; 
lean_dec(v_a_220_);
lean_dec(v_prio_202_);
if (v_isShared_223_ == 0)
{
lean_ctor_set_tag(v___x_222_, 1);
lean_ctor_set(v___x_222_, 0, v_declName_199_);
v___x_294_ = v___x_222_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_declName_199_);
v___x_294_ = v_reuseFailAlloc_305_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_303_; 
v___x_295_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(v_ext_198_, v___x_294_, v_attrKind_203_, v___y_216_, v___y_217_, v___y_218_);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_303_ == 0)
{
lean_object* v_unused_304_; 
v_unused_304_ = lean_ctor_get(v___x_295_, 0);
lean_dec(v_unused_304_);
v___x_297_ = v___x_295_;
v_isShared_298_ = v_isSharedCheck_303_;
goto v_resetjp_296_;
}
else
{
lean_dec(v___x_295_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_303_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_299_ = lean_box(v___x_213_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v___x_299_);
v___x_301_ = v___x_297_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
}
}
else
{
lean_dec(v_prio_202_);
lean_dec(v_declName_199_);
lean_dec_ref(v_ext_198_);
return v___x_219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDeclToUnfold___boxed(lean_object* v_ext_326_, lean_object* v_declName_327_, lean_object* v_post_328_, lean_object* v_inv_329_, lean_object* v_prio_330_, lean_object* v_attrKind_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
uint8_t v_post_boxed_337_; uint8_t v_inv_boxed_338_; uint8_t v_attrKind_boxed_339_; lean_object* v_res_340_; 
v_post_boxed_337_ = lean_unbox(v_post_328_);
v_inv_boxed_338_ = lean_unbox(v_inv_329_);
v_attrKind_boxed_339_ = lean_unbox(v_attrKind_331_);
v_res_340_ = l_Lean_Meta_addDeclToUnfold(v_ext_326_, v_declName_327_, v_post_boxed_337_, v_inv_boxed_338_, v_prio_330_, v_attrKind_boxed_339_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2(lean_object* v_00_u03b1_341_, lean_object* v_00_u03b2_342_, lean_object* v_00_u03c3_343_, lean_object* v_ext_344_, lean_object* v_b_345_, uint8_t v_kind_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg(v_ext_344_, v_b_345_, v_kind_346_, v___y_348_, v___y_349_, v___y_350_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___boxed(lean_object* v_00_u03b1_353_, lean_object* v_00_u03b2_354_, lean_object* v_00_u03c3_355_, lean_object* v_ext_356_, lean_object* v_b_357_, lean_object* v_kind_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
uint8_t v_kind_boxed_364_; lean_object* v_res_365_; 
v_kind_boxed_364_ = lean_unbox(v_kind_358_);
v_res_365_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2(v_00_u03b1_353_, v_00_u03b2_354_, v_00_u03c3_355_, v_ext_356_, v_b_357_, v_kind_boxed_364_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3(lean_object* v_00_u03b1_366_, lean_object* v_msg_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(v_msg_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___boxed(lean_object* v_00_u03b1_374_, lean_object* v_msg_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3(v_00_u03b1_374_, v_msg_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3(lean_object* v_00_u03b2_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2___redArg(){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2___redArg___boxed(lean_object* v___dummy_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2___redArg();
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2(lean_object* v_00_u03b2_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2);
return v___x_389_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__12(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__10));
v___x_417_ = l_Lean_mkAtom(v___x_416_);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__13(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_418_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__12, &l_Lean_Meta_mkSimpAttr___auto__1___closed__12_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__12);
v___x_419_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__5));
v___x_420_ = lean_array_push(v___x_419_, v___x_418_);
return v___x_420_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__18(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__17));
v___x_430_ = l_Lean_mkAtom(v___x_429_);
return v___x_430_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__19(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__18, &l_Lean_Meta_mkSimpAttr___auto__1___closed__18_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__18);
v___x_432_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__5));
v___x_433_ = lean_array_push(v___x_432_, v___x_431_);
return v___x_433_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__20(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_434_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__19, &l_Lean_Meta_mkSimpAttr___auto__1___closed__19_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__19);
v___x_435_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__16));
v___x_436_ = lean_box(2);
v___x_437_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v___x_435_);
lean_ctor_set(v___x_437_, 2, v___x_434_);
return v___x_437_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__21(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__20, &l_Lean_Meta_mkSimpAttr___auto__1___closed__20_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__20);
v___x_439_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__13, &l_Lean_Meta_mkSimpAttr___auto__1___closed__13_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__13);
v___x_440_ = lean_array_push(v___x_439_, v___x_438_);
return v___x_440_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__22(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_441_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__21, &l_Lean_Meta_mkSimpAttr___auto__1___closed__21_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__21);
v___x_442_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__11));
v___x_443_ = lean_box(2);
v___x_444_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___x_442_);
lean_ctor_set(v___x_444_, 2, v___x_441_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__23(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__22, &l_Lean_Meta_mkSimpAttr___auto__1___closed__22_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__22);
v___x_446_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__5));
v___x_447_ = lean_array_push(v___x_446_, v___x_445_);
return v___x_447_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__24(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_448_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__23, &l_Lean_Meta_mkSimpAttr___auto__1___closed__23_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__23);
v___x_449_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__9));
v___x_450_ = lean_box(2);
v___x_451_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
lean_ctor_set(v___x_451_, 1, v___x_449_);
lean_ctor_set(v___x_451_, 2, v___x_448_);
return v___x_451_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__25(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__24, &l_Lean_Meta_mkSimpAttr___auto__1___closed__24_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__24);
v___x_453_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__5));
v___x_454_ = lean_array_push(v___x_453_, v___x_452_);
return v___x_454_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__26(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_455_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__25, &l_Lean_Meta_mkSimpAttr___auto__1___closed__25_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__25);
v___x_456_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__7));
v___x_457_ = lean_box(2);
v___x_458_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v___x_456_);
lean_ctor_set(v___x_458_, 2, v___x_455_);
return v___x_458_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__27(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__26, &l_Lean_Meta_mkSimpAttr___auto__1___closed__26_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__26);
v___x_460_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__5));
v___x_461_ = lean_array_push(v___x_460_, v___x_459_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__28(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_462_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__27, &l_Lean_Meta_mkSimpAttr___auto__1___closed__27_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__27);
v___x_463_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__4));
v___x_464_ = lean_box(2);
v___x_465_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v___x_463_);
lean_ctor_set(v___x_465_, 2, v___x_462_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___auto__1(void){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__28, &l_Lean_Meta_mkSimpAttr___auto__1___closed__28_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__28);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__0);
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0);
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
lean_ctor_set(v___x_471_, 2, v___x_470_);
lean_ctor_set(v___x_471_, 3, v___x_470_);
lean_ctor_set(v___x_471_, 4, v___x_469_);
lean_ctor_set(v___x_471_, 5, v___x_469_);
lean_ctor_set(v___x_471_, 6, v___x_469_);
lean_ctor_set(v___x_471_, 7, v___x_469_);
lean_ctor_set(v___x_471_, 8, v___x_469_);
lean_ctor_set(v___x_471_, 9, v___x_469_);
lean_ctor_set(v___x_471_, 10, v___x_469_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = lean_unsigned_to_nat(32u);
v___x_473_ = lean_mk_empty_array_with_capacity(v___x_472_);
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3(void){
_start:
{
size_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_475_ = ((size_t)5ULL);
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_unsigned_to_nat(32u);
v___x_478_ = lean_mk_empty_array_with_capacity(v___x_477_);
v___x_479_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__2);
v___x_480_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_480_, 0, v___x_479_);
lean_ctor_set(v___x_480_, 1, v___x_478_);
lean_ctor_set(v___x_480_, 2, v___x_476_);
lean_ctor_set(v___x_480_, 3, v___x_476_);
lean_ctor_set_usize(v___x_480_, 4, v___x_475_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_481_ = lean_box(1);
v___x_482_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3);
v___x_483_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__0);
v___x_484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
lean_ctor_set(v___x_484_, 1, v___x_482_);
lean_ctor_set(v___x_484_, 2, v___x_481_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__5));
v___x_487_ = l_Lean_stringToMessageData(v___x_486_);
return v___x_487_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__8(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__7));
v___x_490_ = l_Lean_stringToMessageData(v___x_489_);
return v___x_490_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__10(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__9));
v___x_493_ = l_Lean_stringToMessageData(v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__12(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__11));
v___x_496_ = l_Lean_stringToMessageData(v___x_495_);
return v___x_496_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__14(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__13));
v___x_499_ = l_Lean_stringToMessageData(v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__16(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__15));
v___x_502_ = l_Lean_stringToMessageData(v___x_501_);
return v___x_502_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__18(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__17));
v___x_505_ = l_Lean_stringToMessageData(v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg(lean_object* v_msg_506_, lean_object* v_declHint_507_, lean_object* v___y_508_){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v_env_512_; uint8_t v___x_513_; 
v___x_510_ = lean_box(0);
v___x_511_ = lean_st_ref_get(v___y_508_);
v_env_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc_ref(v_env_512_);
lean_dec(v___x_511_);
v___x_513_ = l_Lean_Name_isAnonymous(v_declHint_507_);
if (v___x_513_ == 0)
{
uint8_t v_isExporting_514_; 
v_isExporting_514_ = lean_ctor_get_uint8(v_env_512_, sizeof(void*)*13);
if (v_isExporting_514_ == 0)
{
lean_object* v___x_515_; 
lean_dec_ref(v_env_512_);
lean_dec(v_declHint_507_);
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v_msg_506_);
return v___x_515_;
}
else
{
lean_object* v___x_516_; uint8_t v___x_517_; 
lean_inc_ref(v_env_512_);
v___x_516_ = l_Lean_Environment_setExporting(v_env_512_, v___x_513_);
lean_inc(v_declHint_507_);
lean_inc_ref(v___x_516_);
v___x_517_ = l_Lean_Environment_contains(v___x_516_, v_declHint_507_, v_isExporting_514_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; 
lean_dec_ref(v___x_516_);
lean_dec_ref(v_env_512_);
lean_dec(v_declHint_507_);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v_msg_506_);
return v___x_518_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v_c_524_; lean_object* v___x_525_; 
v___x_519_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1);
v___x_520_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4);
v___x_521_ = l_Lean_Options_empty;
lean_inc_ref(v___x_516_);
v___x_522_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_522_, 0, v___x_516_);
lean_ctor_set(v___x_522_, 1, v___x_519_);
lean_ctor_set(v___x_522_, 2, v___x_520_);
lean_ctor_set(v___x_522_, 3, v___x_521_);
lean_inc(v_declHint_507_);
v___x_523_ = l_Lean_MessageData_ofConstName(v_declHint_507_, v___x_513_);
v_c_524_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_524_, 0, v___x_522_);
lean_ctor_set(v_c_524_, 1, v___x_523_);
v___x_525_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_516_, v_declHint_507_);
lean_dec_ref(v___x_516_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
lean_dec_ref(v_env_512_);
lean_dec(v_declHint_507_);
v___x_526_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6);
v___x_527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v_c_524_);
v___x_528_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__8);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = l_Lean_MessageData_note(v___x_529_);
v___x_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_531_, 0, v_msg_506_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
else
{
lean_object* v_val_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_567_; 
v_val_533_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_567_ == 0)
{
v___x_535_ = v___x_525_;
v_isShared_536_ = v_isSharedCheck_567_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_val_533_);
lean_dec(v___x_525_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_567_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v_moduleNames_538_; lean_object* v_mod_539_; uint8_t v___x_540_; 
v___x_537_ = l_Lean_Environment_header(v_env_512_);
lean_dec_ref(v_env_512_);
v_moduleNames_538_ = lean_ctor_get(v___x_537_, 4);
lean_inc_ref(v_moduleNames_538_);
lean_dec_ref(v___x_537_);
v_mod_539_ = lean_array_get(v___x_510_, v_moduleNames_538_, v_val_533_);
lean_dec(v_val_533_);
lean_dec_ref(v_moduleNames_538_);
v___x_540_ = l_Lean_isPrivateName(v_declHint_507_);
lean_dec(v_declHint_507_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_541_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__10);
v___x_542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v_c_524_);
v___x_543_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__12);
v___x_544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_542_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = l_Lean_MessageData_ofName(v_mod_539_);
v___x_546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_544_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__14);
v___x_548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_546_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = l_Lean_MessageData_note(v___x_548_);
v___x_550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_550_, 0, v_msg_506_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
if (v_isShared_536_ == 0)
{
lean_ctor_set_tag(v___x_535_, 0);
lean_ctor_set(v___x_535_, 0, v___x_550_);
v___x_552_ = v___x_535_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_554_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__6);
v___x_555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set(v___x_555_, 1, v_c_524_);
v___x_556_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__16);
v___x_557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = l_Lean_MessageData_ofName(v_mod_539_);
v___x_559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_557_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__18);
v___x_561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = l_Lean_MessageData_note(v___x_561_);
v___x_563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_563_, 0, v_msg_506_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
if (v_isShared_536_ == 0)
{
lean_ctor_set_tag(v___x_535_, 0);
lean_ctor_set(v___x_535_, 0, v___x_563_);
v___x_565_ = v___x_535_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
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
lean_object* v___x_568_; 
lean_dec_ref(v_env_512_);
lean_dec(v_declHint_507_);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v_msg_506_);
return v___x_568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_msg_569_, lean_object* v_declHint_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg(v_msg_569_, v_declHint_570_, v___y_571_);
lean_dec(v___y_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object* v_msg_574_, lean_object* v_declHint_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v___x_581_; lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_591_; 
v___x_581_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg(v_msg_574_, v_declHint_575_, v___y_579_);
v_a_582_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_591_ == 0)
{
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_591_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_591_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_586_ = l_Lean_unknownIdentifierMessageTag;
v___x_587_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v_a_582_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_587_);
v___x_589_ = v___x_584_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_msg_592_, lean_object* v_declHint_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6(v_msg_592_, v_declHint_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_ref_600_, lean_object* v_msg_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v_toCold_607_; lean_object* v_currRecDepth_608_; lean_object* v_ref_609_; uint16_t v_optionFlags_610_; uint8_t v_suppressElabErrors_611_; uint8_t v_checkDeprecated_612_; uint8_t v_isRecordingDeps_613_; lean_object* v_ref_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v_toCold_607_ = lean_ctor_get(v___y_604_, 0);
v_currRecDepth_608_ = lean_ctor_get(v___y_604_, 1);
v_ref_609_ = lean_ctor_get(v___y_604_, 2);
v_optionFlags_610_ = lean_ctor_get_uint16(v___y_604_, sizeof(void*)*3);
v_suppressElabErrors_611_ = lean_ctor_get_uint8(v___y_604_, sizeof(void*)*3 + 2);
v_checkDeprecated_612_ = lean_ctor_get_uint8(v___y_604_, sizeof(void*)*3 + 3);
v_isRecordingDeps_613_ = lean_ctor_get_uint8(v___y_604_, sizeof(void*)*3 + 4);
v_ref_614_ = l_Lean_replaceRef(v_ref_600_, v_ref_609_);
lean_inc(v_currRecDepth_608_);
lean_inc_ref(v_toCold_607_);
v___x_615_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_615_, 0, v_toCold_607_);
lean_ctor_set(v___x_615_, 1, v_currRecDepth_608_);
lean_ctor_set(v___x_615_, 2, v_ref_614_);
lean_ctor_set_uint16(v___x_615_, sizeof(void*)*3, v_optionFlags_610_);
lean_ctor_set_uint8(v___x_615_, sizeof(void*)*3 + 2, v_suppressElabErrors_611_);
lean_ctor_set_uint8(v___x_615_, sizeof(void*)*3 + 3, v_checkDeprecated_612_);
lean_ctor_set_uint8(v___x_615_, sizeof(void*)*3 + 4, v_isRecordingDeps_613_);
v___x_616_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(v_msg_601_, v___y_602_, v___y_603_, v___x_615_, v___y_605_);
lean_dec_ref_known(v___x_615_, 3);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_ref_617_, lean_object* v_msg_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ref_617_, v_msg_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v_ref_617_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_625_, lean_object* v_msg_626_, lean_object* v_declHint_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; lean_object* v_a_634_; lean_object* v___x_635_; 
v___x_633_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6(v_msg_626_, v_declHint_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref(v___x_633_);
v___x_635_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ref_625_, v_a_634_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_636_, lean_object* v_msg_637_, lean_object* v_declHint_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_636_, v_msg_637_, v_declHint_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v_ref_636_);
return v_res_644_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_647_ = l_Lean_stringToMessageData(v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_650_ = l_Lean_stringToMessageData(v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_651_, lean_object* v_constName_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v___x_658_; uint8_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_658_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_659_ = 0;
lean_inc(v_constName_652_);
v___x_660_ = l_Lean_MessageData_ofConstName(v_constName_652_, v___x_659_);
v___x_661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_658_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_661_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_651_, v___x_663_, v_constName_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_665_, lean_object* v_constName_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(v_ref_665_, v_constName_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v_ref_665_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(lean_object* v_constName_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_ref_679_; lean_object* v___x_680_; 
v_ref_679_ = lean_ctor_get(v___y_676_, 2);
v___x_680_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(v_ref_679_, v_constName_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg___boxed(lean_object* v_constName_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(v_constName_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0(lean_object* v_constName_688_, uint8_t v_skipRealize_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v___x_695_; lean_object* v_env_696_; lean_object* v___x_697_; 
v___x_695_ = lean_st_ref_get(v___y_693_);
v_env_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc_ref(v_env_696_);
lean_dec(v___x_695_);
lean_inc(v_constName_688_);
v___x_697_ = l_Lean_Environment_findAsync_x3f(v_env_696_, v_constName_688_, v_skipRealize_689_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(v_constName_688_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
return v___x_698_;
}
else
{
lean_object* v_val_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec(v_constName_688_);
v_val_699_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_697_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_val_699_);
lean_dec(v___x_697_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set_tag(v___x_701_, 0);
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_val_699_);
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
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0___boxed(lean_object* v_constName_707_, lean_object* v_skipRealize_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
uint8_t v_skipRealize_boxed_714_; lean_object* v_res_715_; 
v_skipRealize_boxed_714_ = lean_unbox(v_skipRealize_708_);
v_res_715_ = l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0(v_constName_707_, v_skipRealize_boxed_714_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
return v_res_715_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__0(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__0);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
return v___x_717_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_718_ = lean_box(1);
v___x_719_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3);
v___x_720_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__0, &l_Lean_Meta_mkSimpAttr___lam__0___closed__0_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__0);
v___x_721_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set(v___x_721_, 1, v___x_719_);
lean_ctor_set(v___x_721_, 2, v___x_718_);
return v___x_721_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__3(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_724_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__0, &l_Lean_Meta_mkSimpAttr___lam__0___closed__0_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__0);
v___x_725_ = lean_unsigned_to_nat(0u);
v___x_726_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
lean_ctor_set(v___x_726_, 2, v___x_725_);
lean_ctor_set(v___x_726_, 3, v___x_725_);
lean_ctor_set(v___x_726_, 4, v___x_724_);
lean_ctor_set(v___x_726_, 5, v___x_724_);
lean_ctor_set(v___x_726_, 6, v___x_724_);
lean_ctor_set(v___x_726_, 7, v___x_724_);
lean_ctor_set(v___x_726_, 8, v___x_724_);
lean_ctor_set(v___x_726_, 9, v___x_724_);
lean_ctor_set(v___x_726_, 10, v___x_724_);
return v___x_726_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__4(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__0, &l_Lean_Meta_mkSimpAttr___lam__0___closed__0_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__0);
v___x_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
return v___x_728_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = lean_unsigned_to_nat(0u);
v___x_730_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__0, &l_Lean_Meta_mkSimpAttr___lam__0___closed__0_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__0);
v___x_731_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
lean_ctor_set(v___x_731_, 2, v___x_729_);
return v___x_731_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_732_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__5, &l_Lean_Meta_mkSimpAttr___lam__0___closed__5_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__5);
v___x_733_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__4, &l_Lean_Meta_mkSimpAttr___lam__0___closed__4_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__4);
v___x_734_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__0, &l_Lean_Meta_mkSimpAttr___lam__0___closed__0_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__0);
v___x_735_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2);
v___x_736_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
lean_ctor_set(v___x_736_, 1, v___x_734_);
lean_ctor_set(v___x_736_, 2, v___x_733_);
lean_ctor_set(v___x_736_, 3, v___x_734_);
lean_ctor_set(v___x_736_, 4, v___x_734_);
lean_ctor_set(v___x_736_, 5, v___x_734_);
lean_ctor_set(v___x_736_, 6, v___x_734_);
lean_ctor_set(v___x_736_, 7, v___x_732_);
return v___x_736_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__7(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__0, &l_Lean_Meta_mkSimpAttr___lam__0___closed__0_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__0);
v___x_738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
lean_ctor_set(v___x_738_, 2, v___x_737_);
lean_ctor_set(v___x_738_, 3, v___x_737_);
lean_ctor_set(v___x_738_, 4, v___x_737_);
return v___x_738_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__9(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__8));
v___x_741_ = l_Lean_stringToMessageData(v___x_740_);
return v___x_741_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__11(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__10));
v___x_744_ = l_Lean_stringToMessageData(v___x_743_);
return v___x_744_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__13(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__12));
v___x_747_ = l_Lean_stringToMessageData(v___x_746_);
return v___x_747_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__14(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__13, &l_Lean_Meta_mkSimpAttr___lam__0___closed__13_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__13);
v___x_749_ = l_Lean_MessageData_note(v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__0(lean_object* v_attrName_756_, lean_object* v___x_757_, lean_object* v_ext_758_, lean_object* v_declName_759_, lean_object* v_stx_760_, uint8_t v_attrKind_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v___x_768_; 
lean_inc(v_declName_759_);
v___x_768_ = l_Lean_Meta_Simp_isSimproc___redArg(v_declName_759_, v___y_763_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; uint8_t v___x_770_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_768_, 1);
v___x_770_ = lean_unbox(v_a_769_);
lean_dec(v_a_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_Meta_Simp_isBuiltinSimproc___redArg(v_declName_759_, v___y_763_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_887_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_887_ == 0)
{
v___x_774_ = v___x_771_;
v_isShared_775_ = v_isSharedCheck_887_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_771_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_887_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
uint8_t v___x_776_; 
v___x_776_ = lean_unbox(v_a_772_);
if (v___x_776_ == 0)
{
uint8_t v___x_777_; uint8_t v___x_778_; uint8_t v___x_779_; uint8_t v___x_780_; lean_object* v___x_781_; uint8_t v___x_782_; uint8_t v___x_783_; uint8_t v___x_784_; uint8_t v___x_785_; uint8_t v___x_786_; uint8_t v___x_787_; uint8_t v___x_788_; uint64_t v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; uint8_t v___x_798_; uint8_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___y_812_; uint8_t v___x_813_; lean_object* v___x_814_; 
lean_dec(v_attrName_756_);
v___x_777_ = 1;
v___x_778_ = 1;
v___x_779_ = 0;
v___x_780_ = 2;
v___x_781_ = lean_alloc_ctor(0, 0, 20);
v___x_782_ = lean_unbox(v_a_772_);
lean_ctor_set_uint8(v___x_781_, 0, v___x_782_);
v___x_783_ = lean_unbox(v_a_772_);
lean_ctor_set_uint8(v___x_781_, 1, v___x_783_);
v___x_784_ = lean_unbox(v_a_772_);
lean_ctor_set_uint8(v___x_781_, 2, v___x_784_);
v___x_785_ = lean_unbox(v_a_772_);
lean_ctor_set_uint8(v___x_781_, 3, v___x_785_);
v___x_786_ = lean_unbox(v_a_772_);
lean_ctor_set_uint8(v___x_781_, 4, v___x_786_);
lean_ctor_set_uint8(v___x_781_, 5, v___x_777_);
lean_ctor_set_uint8(v___x_781_, 6, v___x_777_);
v___x_787_ = lean_unbox(v_a_772_);
lean_ctor_set_uint8(v___x_781_, 7, v___x_787_);
lean_ctor_set_uint8(v___x_781_, 8, v___x_777_);
lean_ctor_set_uint8(v___x_781_, 9, v___x_778_);
lean_ctor_set_uint8(v___x_781_, 10, v___x_779_);
lean_ctor_set_uint8(v___x_781_, 11, v___x_777_);
lean_ctor_set_uint8(v___x_781_, 12, v___x_777_);
lean_ctor_set_uint8(v___x_781_, 13, v___x_777_);
lean_ctor_set_uint8(v___x_781_, 14, v___x_780_);
lean_ctor_set_uint8(v___x_781_, 15, v___x_777_);
lean_ctor_set_uint8(v___x_781_, 16, v___x_777_);
lean_ctor_set_uint8(v___x_781_, 17, v___x_777_);
lean_ctor_set_uint8(v___x_781_, 18, v___x_777_);
v___x_788_ = lean_unbox(v_a_772_);
lean_ctor_set_uint8(v___x_781_, 19, v___x_788_);
v___x_789_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_781_);
v___x_790_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_790_, 0, v___x_781_);
lean_ctor_set_uint64(v___x_790_, sizeof(void*)*1, v___x_789_);
v___x_791_ = lean_unsigned_to_nat(0u);
v___x_792_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__3);
v___x_793_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__1, &l_Lean_Meta_mkSimpAttr___lam__0___closed__1_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__1);
v___x_794_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__2));
v___x_795_ = lean_box(0);
lean_inc(v___x_757_);
v___x_796_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_796_, 0, v___x_790_);
lean_ctor_set(v___x_796_, 1, v___x_757_);
lean_ctor_set(v___x_796_, 2, v___x_793_);
lean_ctor_set(v___x_796_, 3, v___x_794_);
lean_ctor_set(v___x_796_, 4, v___x_795_);
lean_ctor_set(v___x_796_, 5, v___x_791_);
lean_ctor_set(v___x_796_, 6, v___x_795_);
v___x_797_ = lean_unbox(v_a_772_);
lean_ctor_set_uint8(v___x_796_, sizeof(void*)*7, v___x_797_);
v___x_798_ = lean_unbox(v_a_772_);
lean_ctor_set_uint8(v___x_796_, sizeof(void*)*7 + 1, v___x_798_);
v___x_799_ = lean_unbox(v_a_772_);
lean_ctor_set_uint8(v___x_796_, sizeof(void*)*7 + 2, v___x_799_);
lean_ctor_set_uint8(v___x_796_, sizeof(void*)*7 + 3, v___x_777_);
v___x_800_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__3, &l_Lean_Meta_mkSimpAttr___lam__0___closed__3_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__3);
v___x_801_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__6, &l_Lean_Meta_mkSimpAttr___lam__0___closed__6_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__6);
v___x_802_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__7, &l_Lean_Meta_mkSimpAttr___lam__0___closed__7_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__7);
v___x_803_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_803_, 0, v___x_800_);
lean_ctor_set(v___x_803_, 1, v___x_801_);
lean_ctor_set(v___x_803_, 2, v___x_757_);
lean_ctor_set(v___x_803_, 3, v___x_792_);
lean_ctor_set(v___x_803_, 4, v___x_802_);
v___x_804_ = lean_box(0);
v___x_805_ = lean_st_mk_ref(v___x_803_);
v___x_813_ = lean_unbox(v_a_772_);
lean_inc(v_declName_759_);
v___x_814_ = l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0(v_declName_759_, v___x_813_, v___x_796_, v___x_805_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; uint8_t v___y_817_; uint8_t v___y_818_; uint8_t v___y_867_; lean_object* v___x_872_; lean_object* v___x_873_; uint8_t v___x_874_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
lean_dec_ref_known(v___x_814_, 1);
v___x_872_ = lean_unsigned_to_nat(1u);
v___x_873_ = l_Lean_Syntax_getArg(v_stx_760_, v___x_872_);
v___x_874_ = l_Lean_Syntax_isNone(v___x_873_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_875_ = l_Lean_Syntax_getArg(v___x_873_, v___x_791_);
lean_dec(v___x_873_);
v___x_876_ = l_Lean_Syntax_getKind(v___x_875_);
v___x_877_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__16));
v___x_878_ = lean_name_eq(v___x_876_, v___x_877_);
lean_dec(v___x_876_);
v___y_867_ = v___x_878_;
goto v___jp_866_;
}
else
{
lean_dec(v___x_873_);
v___y_867_ = v___x_777_;
goto v___jp_866_;
}
v___jp_816_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_819_ = lean_unsigned_to_nat(3u);
v___x_820_ = l_Lean_Syntax_getArg(v_stx_760_, v___x_819_);
lean_dec(v_stx_760_);
v___x_821_ = l_Lean_getAttrParamOptPrio(v___x_820_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v_sig_823_; lean_object* v___x_824_; lean_object* v_type_825_; lean_object* v___x_826_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_a_822_);
lean_dec_ref_known(v___x_821_, 1);
v_sig_823_ = lean_ctor_get(v_a_815_, 1);
lean_inc_ref(v_sig_823_);
lean_dec(v_a_815_);
v___x_824_ = lean_task_get_own(v_sig_823_);
v_type_825_ = lean_ctor_get(v___x_824_, 2);
lean_inc_ref(v_type_825_);
lean_dec(v___x_824_);
v___x_826_ = l_Lean_Meta_isProp(v_type_825_, v___x_796_, v___x_805_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; uint8_t v___x_828_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_a_827_);
lean_dec_ref_known(v___x_826_, 1);
v___x_828_ = lean_unbox(v_a_827_);
lean_dec(v_a_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; 
lean_inc(v_declName_759_);
v___x_829_ = l_Lean_Meta_addDeclToUnfold(v_ext_758_, v_declName_759_, v___y_817_, v___y_818_, v_a_822_, v_attrKind_761_, v___x_796_, v___x_805_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; uint8_t v___x_831_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
lean_dec_ref_known(v___x_829_, 1);
v___x_831_ = lean_unbox(v_a_830_);
lean_dec(v_a_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; uint8_t v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_832_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__9, &l_Lean_Meta_mkSimpAttr___lam__0___closed__9_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__9);
v___x_833_ = lean_unbox(v_a_772_);
lean_dec(v_a_772_);
v___x_834_ = l_Lean_MessageData_ofConstName(v_declName_759_, v___x_833_);
v___x_835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_832_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__11, &l_Lean_Meta_mkSimpAttr___lam__0___closed__11_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__11);
v___x_837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__14, &l_Lean_Meta_mkSimpAttr___lam__0___closed__14_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__14);
v___x_839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_837_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(v___x_839_, v___x_796_, v___x_805_, v___y_762_, v___y_763_);
lean_dec_ref_known(v___x_796_, 7);
v___y_812_ = v___x_840_;
goto v___jp_811_;
}
else
{
lean_dec_ref_known(v___x_796_, 7);
lean_dec(v_a_772_);
lean_dec(v_declName_759_);
goto v___jp_806_;
}
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_dec(v___x_805_);
lean_dec_ref_known(v___x_796_, 7);
lean_del_object(v___x_774_);
lean_dec(v_a_772_);
lean_dec(v_declName_759_);
v_a_841_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_829_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_829_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
else
{
lean_object* v___x_849_; 
lean_dec(v_a_772_);
v___x_849_ = l_Lean_Meta_addSimpTheorem(v_ext_758_, v_declName_759_, v___y_817_, v___y_818_, v_attrKind_761_, v_a_822_, v___x_796_, v___x_805_, v___y_762_, v___y_763_);
lean_dec_ref_known(v___x_796_, 7);
v___y_812_ = v___x_849_;
goto v___jp_811_;
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec(v_a_822_);
lean_dec(v___x_805_);
lean_dec_ref_known(v___x_796_, 7);
lean_del_object(v___x_774_);
lean_dec(v_a_772_);
lean_dec(v_declName_759_);
lean_dec_ref(v_ext_758_);
v_a_850_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_826_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_826_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec(v_a_815_);
lean_dec(v___x_805_);
lean_dec_ref_known(v___x_796_, 7);
lean_del_object(v___x_774_);
lean_dec(v_a_772_);
lean_dec(v_declName_759_);
lean_dec_ref(v_ext_758_);
v_a_858_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_821_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_821_);
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
v___jp_866_:
{
lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_868_ = lean_unsigned_to_nat(2u);
v___x_869_ = l_Lean_Syntax_getArg(v_stx_760_, v___x_868_);
v___x_870_ = l_Lean_Syntax_isNone(v___x_869_);
lean_dec(v___x_869_);
if (v___x_870_ == 0)
{
v___y_817_ = v___y_867_;
v___y_818_ = v___x_777_;
goto v___jp_816_;
}
else
{
uint8_t v___x_871_; 
v___x_871_ = lean_unbox(v_a_772_);
v___y_817_ = v___y_867_;
v___y_818_ = v___x_871_;
goto v___jp_816_;
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_dec(v___x_805_);
lean_dec_ref_known(v___x_796_, 7);
lean_del_object(v___x_774_);
lean_dec(v_a_772_);
lean_dec(v_stx_760_);
lean_dec(v_declName_759_);
lean_dec_ref(v_ext_758_);
v_a_879_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_814_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_814_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
v___jp_806_:
{
lean_object* v___x_807_; lean_object* v___x_809_; 
v___x_807_ = lean_st_ref_get(v___x_805_);
lean_dec(v___x_805_);
lean_dec(v___x_807_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_804_);
v___x_809_ = v___x_774_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
v___jp_811_:
{
if (lean_obj_tag(v___y_812_) == 0)
{
lean_dec_ref_known(v___y_812_, 1);
goto v___jp_806_;
}
else
{
lean_dec(v___x_805_);
lean_del_object(v___x_774_);
return v___y_812_;
}
}
}
else
{
lean_del_object(v___x_774_);
lean_dec(v_a_772_);
lean_dec_ref(v_ext_758_);
lean_dec(v___x_757_);
goto v___jp_765_;
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec(v_stx_760_);
lean_dec(v_declName_759_);
lean_dec_ref(v_ext_758_);
lean_dec(v___x_757_);
lean_dec(v_attrName_756_);
v_a_888_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_771_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_771_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
else
{
lean_dec_ref(v_ext_758_);
lean_dec(v___x_757_);
goto v___jp_765_;
}
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec(v_stx_760_);
lean_dec(v_declName_759_);
lean_dec_ref(v_ext_758_);
lean_dec(v___x_757_);
lean_dec(v_attrName_756_);
v_a_896_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_768_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_768_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
v___jp_765_:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(v_attrName_756_);
v___x_767_ = l_Lean_Attribute_add(v_declName_759_, v___x_766_, v_stx_760_, v_attrKind_761_, v___y_762_, v___y_763_);
return v___x_767_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__0___boxed(lean_object* v_attrName_904_, lean_object* v___x_905_, lean_object* v_ext_906_, lean_object* v_declName_907_, lean_object* v_stx_908_, lean_object* v_attrKind_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
uint8_t v_attrKind_boxed_913_; lean_object* v_res_914_; 
v_attrKind_boxed_913_ = lean_unbox(v_attrKind_909_);
v_res_914_ = l_Lean_Meta_mkSimpAttr___lam__0(v_attrName_904_, v___x_905_, v_ext_906_, v_declName_907_, v_stx_908_, v_attrKind_boxed_913_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__1(lean_object* v_a_915_, lean_object* v_x_916_){
_start:
{
lean_inc_ref(v_a_915_);
return v_a_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__1___boxed(lean_object* v_a_917_, lean_object* v_x_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_Meta_mkSimpAttr___lam__1(v_a_917_, v_x_918_);
lean_dec_ref(v_x_918_);
lean_dec_ref(v_a_917_);
return v_res_919_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg(lean_object* v_keys_920_, lean_object* v_i_921_, lean_object* v_k_922_){
_start:
{
lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_923_ = lean_array_get_size(v_keys_920_);
v___x_924_ = lean_nat_dec_lt(v_i_921_, v___x_923_);
if (v___x_924_ == 0)
{
lean_dec(v_i_921_);
return v___x_924_;
}
else
{
lean_object* v_k_x27_925_; uint8_t v___x_926_; 
v_k_x27_925_ = lean_array_fget_borrowed(v_keys_920_, v_i_921_);
v___x_926_ = lean_name_eq(v_k_922_, v_k_x27_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_unsigned_to_nat(1u);
v___x_928_ = lean_nat_add(v_i_921_, v___x_927_);
lean_dec(v_i_921_);
v_i_921_ = v___x_928_;
goto _start;
}
else
{
lean_dec(v_i_921_);
return v___x_924_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_keys_930_, lean_object* v_i_931_, lean_object* v_k_932_){
_start:
{
uint8_t v_res_933_; lean_object* v_r_934_; 
v_res_933_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg(v_keys_930_, v_i_931_, v_k_932_);
lean_dec(v_k_932_);
lean_dec_ref(v_keys_930_);
v_r_934_ = lean_box(v_res_933_);
return v_r_934_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg(lean_object* v_x_935_, size_t v_x_936_, lean_object* v_x_937_){
_start:
{
if (lean_obj_tag(v_x_935_) == 0)
{
lean_object* v_es_938_; lean_object* v___x_939_; size_t v___x_940_; size_t v___x_941_; lean_object* v_j_942_; lean_object* v___x_943_; 
v_es_938_ = lean_ctor_get(v_x_935_, 0);
v___x_939_ = lean_box(2);
v___x_940_ = ((size_t)31ULL);
v___x_941_ = lean_usize_land(v_x_936_, v___x_940_);
v_j_942_ = lean_usize_to_nat(v___x_941_);
v___x_943_ = lean_array_get_borrowed(v___x_939_, v_es_938_, v_j_942_);
lean_dec(v_j_942_);
switch(lean_obj_tag(v___x_943_))
{
case 0:
{
lean_object* v_key_944_; uint8_t v___x_945_; 
v_key_944_ = lean_ctor_get(v___x_943_, 0);
v___x_945_ = lean_name_eq(v_x_937_, v_key_944_);
return v___x_945_;
}
case 1:
{
lean_object* v_node_946_; size_t v___x_947_; size_t v___x_948_; 
v_node_946_ = lean_ctor_get(v___x_943_, 0);
v___x_947_ = ((size_t)5ULL);
v___x_948_ = lean_usize_shift_right(v_x_936_, v___x_947_);
v_x_935_ = v_node_946_;
v_x_936_ = v___x_948_;
goto _start;
}
default: 
{
uint8_t v___x_950_; 
v___x_950_ = 0;
return v___x_950_;
}
}
}
else
{
lean_object* v_ks_951_; lean_object* v___x_952_; uint8_t v___x_953_; 
v_ks_951_ = lean_ctor_get(v_x_935_, 0);
v___x_952_ = lean_unsigned_to_nat(0u);
v___x_953_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg(v_ks_951_, v___x_952_, v_x_937_);
return v___x_953_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_954_, lean_object* v_x_955_, lean_object* v_x_956_){
_start:
{
size_t v_x_9419__boxed_957_; uint8_t v_res_958_; lean_object* v_r_959_; 
v_x_9419__boxed_957_ = lean_unbox_usize(v_x_955_);
lean_dec(v_x_955_);
v_res_958_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg(v_x_954_, v_x_9419__boxed_957_, v_x_956_);
lean_dec(v_x_956_);
lean_dec_ref(v_x_954_);
v_r_959_ = lean_box(v_res_958_);
return v_r_959_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg(lean_object* v_x_960_, lean_object* v_x_961_){
_start:
{
uint64_t v___y_963_; 
if (lean_obj_tag(v_x_961_) == 0)
{
uint64_t v___x_966_; 
v___x_966_ = 1723ULL;
v___y_963_ = v___x_966_;
goto v___jp_962_;
}
else
{
uint64_t v_hash_967_; 
v_hash_967_ = lean_ctor_get_uint64(v_x_961_, sizeof(void*)*2);
v___y_963_ = v_hash_967_;
goto v___jp_962_;
}
v___jp_962_:
{
size_t v___x_964_; uint8_t v___x_965_; 
v___x_964_ = lean_uint64_to_usize(v___y_963_);
v___x_965_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg(v_x_960_, v___x_964_, v_x_961_);
return v___x_965_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg___boxed(lean_object* v_x_968_, lean_object* v_x_969_){
_start:
{
uint8_t v_res_970_; lean_object* v_r_971_; 
v_res_970_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg(v_x_968_, v_x_969_);
lean_dec(v_x_969_);
lean_dec_ref(v_x_968_);
v_r_971_ = lean_box(v_res_970_);
return v_r_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__10(lean_object* v_msgData_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v___x_976_; lean_object* v_toCold_977_; lean_object* v_env_978_; lean_object* v_options_979_; uint8_t v___x_980_; lean_object* v_env_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_976_ = lean_st_ref_get(v___y_974_);
v_toCold_977_ = lean_ctor_get(v___y_973_, 0);
v_env_978_ = lean_ctor_get(v___x_976_, 0);
lean_inc_ref(v_env_978_);
lean_dec(v___x_976_);
v_options_979_ = lean_ctor_get(v_toCold_977_, 2);
v___x_980_ = 0;
v_env_981_ = l_Lean_Environment_setRecordingDeps(v_env_978_, v___x_980_);
v___x_982_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__1);
v___x_983_ = lean_unsigned_to_nat(32u);
v___x_984_ = lean_mk_empty_array_with_capacity(v___x_983_);
lean_dec_ref(v___x_984_);
v___x_985_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg___closed__4);
lean_inc_ref(v_options_979_);
v___x_986_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_986_, 0, v_env_981_);
lean_ctor_set(v___x_986_, 1, v___x_982_);
lean_ctor_set(v___x_986_, 2, v___x_985_);
lean_ctor_set(v___x_986_, 3, v_options_979_);
v___x_987_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v_msgData_972_);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__10___boxed(lean_object* v_msgData_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__10(v_msgData_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
return v_res_993_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0(uint8_t v_suppressElabErrors_1001_, lean_object* v_x_1002_){
_start:
{
if (lean_obj_tag(v_x_1002_) == 1)
{
lean_object* v_pre_1003_; 
v_pre_1003_ = lean_ctor_get(v_x_1002_, 0);
switch(lean_obj_tag(v_pre_1003_))
{
case 1:
{
lean_object* v_pre_1004_; 
v_pre_1004_ = lean_ctor_get(v_pre_1003_, 0);
switch(lean_obj_tag(v_pre_1004_))
{
case 0:
{
lean_object* v_str_1005_; lean_object* v_str_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v_str_1005_ = lean_ctor_get(v_x_1002_, 1);
v_str_1006_ = lean_ctor_get(v_pre_1003_, 1);
v___x_1007_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__0));
v___x_1008_ = lean_string_dec_eq(v_str_1006_, v___x_1007_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; uint8_t v___x_1010_; 
v___x_1009_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__2));
v___x_1010_ = lean_string_dec_eq(v_str_1006_, v___x_1009_);
if (v___x_1010_ == 0)
{
return v___x_1010_;
}
else
{
lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___x_1011_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__1));
v___x_1012_ = lean_string_dec_eq(v_str_1005_, v___x_1011_);
if (v___x_1012_ == 0)
{
return v___x_1012_;
}
else
{
return v_suppressElabErrors_1001_;
}
}
}
else
{
lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_1013_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__2));
v___x_1014_ = lean_string_dec_eq(v_str_1005_, v___x_1013_);
if (v___x_1014_ == 0)
{
return v___x_1014_;
}
else
{
return v_suppressElabErrors_1001_;
}
}
}
case 1:
{
lean_object* v_pre_1015_; 
v_pre_1015_ = lean_ctor_get(v_pre_1004_, 0);
if (lean_obj_tag(v_pre_1015_) == 0)
{
lean_object* v_str_1016_; lean_object* v_str_1017_; lean_object* v_str_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v_str_1016_ = lean_ctor_get(v_x_1002_, 1);
v_str_1017_ = lean_ctor_get(v_pre_1003_, 1);
v_str_1018_ = lean_ctor_get(v_pre_1004_, 1);
v___x_1019_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__3));
v___x_1020_ = lean_string_dec_eq(v_str_1018_, v___x_1019_);
if (v___x_1020_ == 0)
{
return v___x_1020_;
}
else
{
lean_object* v___x_1021_; uint8_t v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__4));
v___x_1022_ = lean_string_dec_eq(v_str_1017_, v___x_1021_);
if (v___x_1022_ == 0)
{
return v___x_1022_;
}
else
{
lean_object* v___x_1023_; uint8_t v___x_1024_; 
v___x_1023_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__5));
v___x_1024_ = lean_string_dec_eq(v_str_1016_, v___x_1023_);
if (v___x_1024_ == 0)
{
return v___x_1024_;
}
else
{
return v_suppressElabErrors_1001_;
}
}
}
}
else
{
uint8_t v___x_1025_; 
v___x_1025_ = 0;
return v___x_1025_;
}
}
default: 
{
uint8_t v___x_1026_; 
v___x_1026_ = 0;
return v___x_1026_;
}
}
}
case 0:
{
lean_object* v_str_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
v_str_1027_ = lean_ctor_get(v_x_1002_, 1);
v___x_1028_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___closed__6));
v___x_1029_ = lean_string_dec_eq(v_str_1027_, v___x_1028_);
if (v___x_1029_ == 0)
{
return v___x_1029_;
}
else
{
return v_suppressElabErrors_1001_;
}
}
default: 
{
uint8_t v___x_1030_; 
v___x_1030_ = 0;
return v___x_1030_;
}
}
}
else
{
uint8_t v___x_1031_; 
v___x_1031_ = 0;
return v___x_1031_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_1032_, lean_object* v_x_1033_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1034_; uint8_t v_res_1035_; lean_object* v_r_1036_; 
v_suppressElabErrors_boxed_1034_ = lean_unbox(v_suppressElabErrors_1032_);
v_res_1035_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0(v_suppressElabErrors_boxed_1034_, v_x_1033_);
lean_dec(v_x_1033_);
v_r_1036_ = lean_box(v_res_1035_);
return v_r_1036_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__11(lean_object* v_opts_1037_, lean_object* v_opt_1038_){
_start:
{
lean_object* v_name_1039_; lean_object* v_defValue_1040_; lean_object* v_map_1041_; lean_object* v___x_1042_; 
v_name_1039_ = lean_ctor_get(v_opt_1038_, 0);
v_defValue_1040_ = lean_ctor_get(v_opt_1038_, 1);
v_map_1041_ = lean_ctor_get(v_opts_1037_, 0);
v___x_1042_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1041_, v_name_1039_);
if (lean_obj_tag(v___x_1042_) == 0)
{
uint8_t v___x_1043_; 
v___x_1043_ = lean_unbox(v_defValue_1040_);
return v___x_1043_;
}
else
{
lean_object* v_val_1044_; 
v_val_1044_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_val_1044_);
lean_dec_ref_known(v___x_1042_, 1);
if (lean_obj_tag(v_val_1044_) == 1)
{
uint8_t v_v_1045_; 
v_v_1045_ = lean_ctor_get_uint8(v_val_1044_, 0);
lean_dec_ref_known(v_val_1044_, 0);
return v_v_1045_;
}
else
{
uint8_t v___x_1046_; 
lean_dec(v_val_1044_);
v___x_1046_ = lean_unbox(v_defValue_1040_);
return v___x_1046_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__11___boxed(lean_object* v_opts_1047_, lean_object* v_opt_1048_){
_start:
{
uint8_t v_res_1049_; lean_object* v_r_1050_; 
v_res_1049_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__11(v_opts_1047_, v_opt_1048_);
lean_dec_ref(v_opt_1048_);
lean_dec_ref(v_opts_1047_);
v_r_1050_ = lean_box(v_res_1049_);
return v_r_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6(lean_object* v_ref_1052_, lean_object* v_msgData_1053_, uint8_t v_severity_1054_, uint8_t v_isSilent_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; uint8_t v___y_1063_; lean_object* v___y_1064_; uint8_t v___y_1065_; lean_object* v___y_1066_; lean_object* v_toCold_1067_; lean_object* v___y_1068_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; uint8_t v___y_1100_; lean_object* v___y_1101_; uint8_t v___y_1102_; uint8_t v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1124_; lean_object* v___y_1125_; uint8_t v___y_1126_; lean_object* v___y_1127_; uint8_t v___y_1128_; uint8_t v___y_1129_; lean_object* v___y_1130_; uint8_t v___y_1134_; uint8_t v___y_1135_; uint8_t v___x_1145_; uint8_t v___y_1147_; uint8_t v___x_1153_; 
v___x_1145_ = 2;
v___x_1153_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1054_, v___x_1145_);
if (v___x_1153_ == 0)
{
v___y_1147_ = v___x_1153_;
goto v___jp_1146_;
}
else
{
uint8_t v___x_1154_; 
lean_inc_ref(v_msgData_1053_);
v___x_1154_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1053_);
if (v___x_1154_ == 0)
{
v___y_1147_ = v___x_1154_;
goto v___jp_1146_;
}
else
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
lean_dec_ref(v_msgData_1053_);
v___x_1155_ = lean_box(0);
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
return v___x_1156_;
}
}
v___jp_1059_:
{
lean_object* v_currNamespace_1069_; lean_object* v_openDecls_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v_env_1075_; lean_object* v_nextMacroScope_1076_; lean_object* v_ngen_1077_; lean_object* v_auxDeclNGen_1078_; lean_object* v_traceState_1079_; lean_object* v_cache_1080_; lean_object* v_recordedDeps_1081_; lean_object* v_messages_1082_; lean_object* v_infoState_1083_; lean_object* v_snapshotTasks_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1095_; 
v_currNamespace_1069_ = lean_ctor_get(v_toCold_1067_, 4);
v_openDecls_1070_ = lean_ctor_get(v_toCold_1067_, 5);
lean_inc(v_openDecls_1070_);
lean_inc(v_currNamespace_1069_);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v_currNamespace_1069_);
lean_ctor_set(v___x_1071_, 1, v_openDecls_1070_);
v___x_1072_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
lean_ctor_set(v___x_1072_, 1, v___y_1062_);
lean_inc_ref(v___y_1061_);
lean_inc_ref(v___y_1066_);
v___x_1073_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1073_, 0, v___y_1066_);
lean_ctor_set(v___x_1073_, 1, v___y_1064_);
lean_ctor_set(v___x_1073_, 2, v___y_1060_);
lean_ctor_set(v___x_1073_, 3, v___y_1061_);
lean_ctor_set(v___x_1073_, 4, v___x_1072_);
lean_ctor_set_uint8(v___x_1073_, sizeof(void*)*5, v___y_1065_);
lean_ctor_set_uint8(v___x_1073_, sizeof(void*)*5 + 1, v___y_1063_);
lean_ctor_set_uint8(v___x_1073_, sizeof(void*)*5 + 2, v_isSilent_1055_);
v___x_1074_ = lean_st_ref_take(v___y_1068_);
v_env_1075_ = lean_ctor_get(v___x_1074_, 0);
v_nextMacroScope_1076_ = lean_ctor_get(v___x_1074_, 1);
v_ngen_1077_ = lean_ctor_get(v___x_1074_, 2);
v_auxDeclNGen_1078_ = lean_ctor_get(v___x_1074_, 3);
v_traceState_1079_ = lean_ctor_get(v___x_1074_, 4);
v_cache_1080_ = lean_ctor_get(v___x_1074_, 5);
v_recordedDeps_1081_ = lean_ctor_get(v___x_1074_, 6);
v_messages_1082_ = lean_ctor_get(v___x_1074_, 7);
v_infoState_1083_ = lean_ctor_get(v___x_1074_, 8);
v_snapshotTasks_1084_ = lean_ctor_get(v___x_1074_, 9);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1086_ = v___x_1074_;
v_isShared_1087_ = v_isSharedCheck_1095_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_snapshotTasks_1084_);
lean_inc(v_infoState_1083_);
lean_inc(v_messages_1082_);
lean_inc(v_recordedDeps_1081_);
lean_inc(v_cache_1080_);
lean_inc(v_traceState_1079_);
lean_inc(v_auxDeclNGen_1078_);
lean_inc(v_ngen_1077_);
lean_inc(v_nextMacroScope_1076_);
lean_inc(v_env_1075_);
lean_dec(v___x_1074_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1095_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1088_ = lean_box(0);
v___x_1089_ = l_Lean_MessageLog_add(v___x_1073_, v_messages_1082_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 7, v___x_1089_);
v___x_1091_ = v___x_1086_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_env_1075_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_nextMacroScope_1076_);
lean_ctor_set(v_reuseFailAlloc_1094_, 2, v_ngen_1077_);
lean_ctor_set(v_reuseFailAlloc_1094_, 3, v_auxDeclNGen_1078_);
lean_ctor_set(v_reuseFailAlloc_1094_, 4, v_traceState_1079_);
lean_ctor_set(v_reuseFailAlloc_1094_, 5, v_cache_1080_);
lean_ctor_set(v_reuseFailAlloc_1094_, 6, v_recordedDeps_1081_);
lean_ctor_set(v_reuseFailAlloc_1094_, 7, v___x_1089_);
lean_ctor_set(v_reuseFailAlloc_1094_, 8, v_infoState_1083_);
lean_ctor_set(v_reuseFailAlloc_1094_, 9, v_snapshotTasks_1084_);
v___x_1091_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = lean_st_ref_put(v___y_1068_, v___x_1091_);
v___x_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1088_);
return v___x_1093_;
}
}
}
v___jp_1096_:
{
lean_object* v_fileName_1105_; lean_object* v_fileMap_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1122_; 
v_fileName_1105_ = lean_ctor_get(v___y_1099_, 0);
v_fileMap_1106_ = lean_ctor_get(v___y_1099_, 1);
v___x_1107_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1053_);
v___x_1108_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__10(v___x_1107_, v___y_1056_, v___y_1057_);
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1111_ = v___x_1108_;
v_isShared_1112_ = v_isSharedCheck_1122_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1108_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1122_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_inc_ref_n(v_fileMap_1106_, 2);
v___x_1113_ = l_Lean_FileMap_toPosition(v_fileMap_1106_, v___y_1101_);
lean_dec(v___y_1101_);
v___x_1114_ = l_Lean_FileMap_toPosition(v_fileMap_1106_, v___y_1104_);
lean_dec(v___y_1104_);
v___x_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
v___x_1116_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___closed__0));
if (v___y_1100_ == 0)
{
lean_del_object(v___x_1111_);
lean_dec_ref(v___y_1098_);
v___y_1060_ = v___x_1115_;
v___y_1061_ = v___x_1116_;
v___y_1062_ = v_a_1109_;
v___y_1063_ = v___y_1102_;
v___y_1064_ = v___x_1113_;
v___y_1065_ = v___y_1103_;
v___y_1066_ = v_fileName_1105_;
v_toCold_1067_ = v___y_1097_;
v___y_1068_ = v___y_1057_;
goto v___jp_1059_;
}
else
{
uint8_t v___x_1117_; 
lean_inc(v_a_1109_);
v___x_1117_ = l_Lean_MessageData_hasTag(v___y_1098_, v_a_1109_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1120_; 
lean_dec_ref_known(v___x_1115_, 1);
lean_dec_ref(v___x_1113_);
lean_dec(v_a_1109_);
v___x_1118_ = lean_box(0);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1118_);
v___x_1120_ = v___x_1111_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
else
{
lean_del_object(v___x_1111_);
v___y_1060_ = v___x_1115_;
v___y_1061_ = v___x_1116_;
v___y_1062_ = v_a_1109_;
v___y_1063_ = v___y_1102_;
v___y_1064_ = v___x_1113_;
v___y_1065_ = v___y_1103_;
v___y_1066_ = v_fileName_1105_;
v_toCold_1067_ = v___y_1097_;
v___y_1068_ = v___y_1057_;
goto v___jp_1059_;
}
}
}
}
v___jp_1123_:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_Syntax_getTailPos_x3f(v___y_1127_, v___y_1129_);
lean_dec(v___y_1127_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_inc(v___y_1130_);
v___y_1097_ = v___y_1124_;
v___y_1098_ = v___y_1125_;
v___y_1099_ = v___y_1124_;
v___y_1100_ = v___y_1126_;
v___y_1101_ = v___y_1130_;
v___y_1102_ = v___y_1128_;
v___y_1103_ = v___y_1129_;
v___y_1104_ = v___y_1130_;
goto v___jp_1096_;
}
else
{
lean_object* v_val_1132_; 
v_val_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_val_1132_);
lean_dec_ref_known(v___x_1131_, 1);
v___y_1097_ = v___y_1124_;
v___y_1098_ = v___y_1125_;
v___y_1099_ = v___y_1124_;
v___y_1100_ = v___y_1126_;
v___y_1101_ = v___y_1130_;
v___y_1102_ = v___y_1128_;
v___y_1103_ = v___y_1129_;
v___y_1104_ = v_val_1132_;
goto v___jp_1096_;
}
}
v___jp_1133_:
{
lean_object* v_toCold_1136_; lean_object* v_ref_1137_; uint8_t v_suppressElabErrors_1138_; lean_object* v___x_1139_; lean_object* v___f_1140_; lean_object* v_ref_1141_; lean_object* v___x_1142_; 
v_toCold_1136_ = lean_ctor_get(v___y_1056_, 0);
v_ref_1137_ = lean_ctor_get(v___y_1056_, 2);
v_suppressElabErrors_1138_ = lean_ctor_get_uint8(v___y_1056_, sizeof(void*)*3 + 2);
v___x_1139_ = lean_box(v_suppressElabErrors_1138_);
v___f_1140_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1140_, 0, v___x_1139_);
v_ref_1141_ = l_Lean_replaceRef(v_ref_1052_, v_ref_1137_);
v___x_1142_ = l_Lean_Syntax_getPos_x3f(v_ref_1141_, v___y_1134_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_unsigned_to_nat(0u);
v___y_1124_ = v_toCold_1136_;
v___y_1125_ = v___f_1140_;
v___y_1126_ = v_suppressElabErrors_1138_;
v___y_1127_ = v_ref_1141_;
v___y_1128_ = v___y_1135_;
v___y_1129_ = v___y_1134_;
v___y_1130_ = v___x_1143_;
goto v___jp_1123_;
}
else
{
lean_object* v_val_1144_; 
v_val_1144_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_val_1144_);
lean_dec_ref_known(v___x_1142_, 1);
v___y_1124_ = v_toCold_1136_;
v___y_1125_ = v___f_1140_;
v___y_1126_ = v_suppressElabErrors_1138_;
v___y_1127_ = v_ref_1141_;
v___y_1128_ = v___y_1135_;
v___y_1129_ = v___y_1134_;
v___y_1130_ = v_val_1144_;
goto v___jp_1123_;
}
}
v___jp_1146_:
{
uint8_t v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = 1;
v___x_1149_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1054_, v___x_1148_);
if (v___x_1149_ == 0)
{
v___y_1134_ = v___y_1147_;
v___y_1135_ = v_severity_1054_;
goto v___jp_1133_;
}
else
{
lean_object* v___x_1150_; lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1150_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1056_);
v___x_1151_ = l_Lean_warningAsError;
v___x_1152_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6_spec__11(v___x_1150_, v___x_1151_);
lean_dec_ref(v___x_1150_);
if (v___x_1152_ == 0)
{
v___y_1134_ = v___y_1147_;
v___y_1135_ = v_severity_1054_;
goto v___jp_1133_;
}
else
{
v___y_1134_ = v___y_1147_;
v___y_1135_ = v___x_1145_;
goto v___jp_1133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_ref_1157_, lean_object* v_msgData_1158_, lean_object* v_severity_1159_, lean_object* v_isSilent_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
uint8_t v_severity_boxed_1164_; uint8_t v_isSilent_boxed_1165_; lean_object* v_res_1166_; 
v_severity_boxed_1164_ = lean_unbox(v_severity_1159_);
v_isSilent_boxed_1165_ = lean_unbox(v_isSilent_1160_);
v_res_1166_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6(v_ref_1157_, v_msgData_1158_, v_severity_boxed_1164_, v_isSilent_boxed_1165_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v_ref_1157_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4(lean_object* v_msgData_1167_, uint8_t v_severity_1168_, uint8_t v_isSilent_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_ref_1173_; lean_object* v___x_1174_; 
v_ref_1173_ = lean_ctor_get(v___y_1170_, 2);
v___x_1174_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4_spec__6(v_ref_1173_, v_msgData_1167_, v_severity_1168_, v_isSilent_1169_, v___y_1170_, v___y_1171_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_1175_, lean_object* v_severity_1176_, lean_object* v_isSilent_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
uint8_t v_severity_boxed_1181_; uint8_t v_isSilent_boxed_1182_; lean_object* v_res_1183_; 
v_severity_boxed_1181_ = lean_unbox(v_severity_1176_);
v_isSilent_boxed_1182_ = lean_unbox(v_isSilent_1177_);
v_res_1183_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4(v_msgData_1175_, v_severity_boxed_1181_, v_isSilent_boxed_1182_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2(lean_object* v_msgData_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
uint8_t v___x_1188_; uint8_t v___x_1189_; lean_object* v___x_1190_; 
v___x_1188_ = 1;
v___x_1189_ = 0;
v___x_1190_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2_spec__4(v_msgData_1184_, v___x_1188_, v___x_1189_, v___y_1185_, v___y_1186_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2___boxed(lean_object* v_msgData_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2(v_msgData_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
return v_res_1195_;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = ((lean_object*)(l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__0));
v___x_1198_ = l_Lean_stringToMessageData(v___x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1(lean_object* v_d_1199_, lean_object* v_thmId_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
uint8_t v___x_1243_; 
v___x_1243_ = l_Lean_Meta_SimpTheorems_isLemma(v_d_1199_, v_thmId_1200_);
if (v___x_1243_ == 0)
{
if (lean_obj_tag(v_thmId_1200_) == 0)
{
lean_object* v_declName_1244_; uint8_t v___x_1245_; 
v_declName_1244_ = lean_ctor_get(v_thmId_1200_, 0);
v___x_1245_ = l_Lean_Meta_SimpTheorems_isDeclToUnfold(v_d_1199_, v_declName_1244_);
if (v___x_1245_ == 0)
{
lean_object* v_toUnfoldThms_1246_; uint8_t v___x_1247_; 
v_toUnfoldThms_1246_ = lean_ctor_get(v_d_1199_, 5);
v___x_1247_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg(v_toUnfoldThms_1246_, v_declName_1244_);
if (v___x_1247_ == 0)
{
goto v___jp_1231_;
}
else
{
goto v___jp_1204_;
}
}
else
{
goto v___jp_1204_;
}
}
else
{
goto v___jp_1231_;
}
}
else
{
goto v___jp_1204_;
}
v___jp_1204_:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = l_Lean_Meta_SimpTheorems_eraseCore(v_d_1199_, v_thmId_1200_);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
return v___x_1206_;
}
v___jp_1207_:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1208_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1209_ = l_Lean_Meta_Origin_key(v_thmId_1200_);
lean_dec_ref(v_thmId_1200_);
v___x_1210_ = l_Lean_MessageData_ofName(v___x_1209_);
v___x_1211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1208_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
v___x_1212_ = lean_obj_once(&l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1, &l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1_once, _init_l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___closed__1);
v___x_1213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1211_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__2(v___x_1213_, v___y_1201_, v___y_1202_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1221_ == 0)
{
lean_object* v_unused_1222_; 
v_unused_1222_ = lean_ctor_get(v___x_1214_, 0);
lean_dec(v_unused_1222_);
v___x_1216_ = v___x_1214_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_dec(v___x_1214_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v_d_1199_);
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_d_1199_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec_ref(v_d_1199_);
v_a_1223_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1214_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1214_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
v___jp_1231_:
{
lean_object* v___x_1232_; 
lean_inc_ref(v_thmId_1200_);
v___x_1232_ = l_Lean_Meta_Origin_converse(v_thmId_1200_);
if (lean_obj_tag(v___x_1232_) == 1)
{
lean_object* v_val_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1242_; 
v_val_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1242_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_val_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1242_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
uint8_t v___x_1237_; 
v___x_1237_ = l_Lean_Meta_SimpTheorems_isLemma(v_d_1199_, v_val_1233_);
if (v___x_1237_ == 0)
{
lean_del_object(v___x_1235_);
lean_dec(v_val_1233_);
goto v___jp_1207_;
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1240_; 
lean_dec_ref(v_thmId_1200_);
v___x_1238_ = l_Lean_Meta_SimpTheorems_eraseCore(v_d_1199_, v_val_1233_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set_tag(v___x_1235_, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1238_);
v___x_1240_ = v___x_1235_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
else
{
lean_dec(v___x_1232_);
goto v___jp_1207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1___boxed(lean_object* v_d_1248_, lean_object* v_thmId_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1(v_d_1248_, v_thmId_1249_, v___y_1250_, v___y_1251_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__2(lean_object* v_attrName_1254_, lean_object* v_ext_1255_, lean_object* v___x_1256_, lean_object* v_declName_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v___x_1264_; 
lean_inc(v_declName_1257_);
v___x_1264_ = l_Lean_Meta_Simp_isSimproc___redArg(v_declName_1257_, v___y_1259_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; uint8_t v___x_1266_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1265_);
lean_dec_ref_known(v___x_1264_, 1);
v___x_1266_ = lean_unbox(v_a_1265_);
lean_dec(v_a_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_Meta_Simp_isBuiltinSimproc___redArg(v_declName_1257_, v___y_1259_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; uint8_t v___x_1269_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1267_, 1);
v___x_1269_ = lean_unbox(v_a_1268_);
if (v___x_1269_ == 0)
{
uint8_t v___x_1270_; lean_object* v___x_1271_; lean_object* v_ext_1272_; lean_object* v_toEnvExtension_1273_; lean_object* v_env_1274_; lean_object* v_asyncMode_1275_; uint8_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; lean_object* v___x_1280_; 
lean_dec(v_attrName_1254_);
v___x_1270_ = 1;
v___x_1271_ = lean_st_ref_get(v___y_1259_);
v_ext_1272_ = lean_ctor_get(v_ext_1255_, 1);
v_toEnvExtension_1273_ = lean_ctor_get(v_ext_1272_, 0);
v_env_1274_ = lean_ctor_get(v___x_1271_, 0);
lean_inc_ref(v_env_1274_);
lean_dec(v___x_1271_);
v_asyncMode_1275_ = lean_ctor_get(v_toEnvExtension_1273_, 2);
v___x_1276_ = lean_unbox(v_a_1268_);
v___x_1277_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1256_, v_ext_1255_, v_env_1274_, v_asyncMode_1275_, v___x_1276_);
v___x_1278_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1278_, 0, v_declName_1257_);
lean_ctor_set_uint8(v___x_1278_, sizeof(void*)*1, v___x_1270_);
v___x_1279_ = lean_unbox(v_a_1268_);
lean_dec(v_a_1268_);
lean_ctor_set_uint8(v___x_1278_, sizeof(void*)*1 + 1, v___x_1279_);
v___x_1280_ = l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1(v___x_1277_, v___x_1278_, v___y_1258_, v___y_1259_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1311_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1311_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1311_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___f_1285_; lean_object* v___x_1286_; lean_object* v_env_1287_; lean_object* v_nextMacroScope_1288_; lean_object* v_ngen_1289_; lean_object* v_auxDeclNGen_1290_; lean_object* v_traceState_1291_; lean_object* v_recordedDeps_1292_; lean_object* v_messages_1293_; lean_object* v_infoState_1294_; lean_object* v_snapshotTasks_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1309_; 
v___f_1285_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1285_, 0, v_a_1281_);
v___x_1286_ = lean_st_ref_take(v___y_1259_);
v_env_1287_ = lean_ctor_get(v___x_1286_, 0);
v_nextMacroScope_1288_ = lean_ctor_get(v___x_1286_, 1);
v_ngen_1289_ = lean_ctor_get(v___x_1286_, 2);
v_auxDeclNGen_1290_ = lean_ctor_get(v___x_1286_, 3);
v_traceState_1291_ = lean_ctor_get(v___x_1286_, 4);
v_recordedDeps_1292_ = lean_ctor_get(v___x_1286_, 6);
v_messages_1293_ = lean_ctor_get(v___x_1286_, 7);
v_infoState_1294_ = lean_ctor_get(v___x_1286_, 8);
v_snapshotTasks_1295_ = lean_ctor_get(v___x_1286_, 9);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1309_ == 0)
{
lean_object* v_unused_1310_; 
v_unused_1310_ = lean_ctor_get(v___x_1286_, 5);
lean_dec(v_unused_1310_);
v___x_1297_ = v___x_1286_;
v_isShared_1298_ = v_isSharedCheck_1309_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_snapshotTasks_1295_);
lean_inc(v_infoState_1294_);
lean_inc(v_messages_1293_);
lean_inc(v_recordedDeps_1292_);
lean_inc(v_traceState_1291_);
lean_inc(v_auxDeclNGen_1290_);
lean_inc(v_ngen_1289_);
lean_inc(v_nextMacroScope_1288_);
lean_inc(v_env_1287_);
lean_dec(v___x_1286_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1309_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1299_ = lean_box(0);
v___x_1300_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1255_, v_env_1287_, v___f_1285_);
v___x_1301_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 5, v___x_1301_);
lean_ctor_set(v___x_1297_, 0, v___x_1300_);
v___x_1303_ = v___x_1297_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1300_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_nextMacroScope_1288_);
lean_ctor_set(v_reuseFailAlloc_1308_, 2, v_ngen_1289_);
lean_ctor_set(v_reuseFailAlloc_1308_, 3, v_auxDeclNGen_1290_);
lean_ctor_set(v_reuseFailAlloc_1308_, 4, v_traceState_1291_);
lean_ctor_set(v_reuseFailAlloc_1308_, 5, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1308_, 6, v_recordedDeps_1292_);
lean_ctor_set(v_reuseFailAlloc_1308_, 7, v_messages_1293_);
lean_ctor_set(v_reuseFailAlloc_1308_, 8, v_infoState_1294_);
lean_ctor_set(v_reuseFailAlloc_1308_, 9, v_snapshotTasks_1295_);
v___x_1303_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1304_; lean_object* v___x_1306_; 
v___x_1304_ = lean_st_ref_put(v___y_1259_, v___x_1303_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1299_);
v___x_1306_ = v___x_1283_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1299_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec_ref(v_ext_1255_);
v_a_1312_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1280_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1280_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
else
{
lean_dec(v_a_1268_);
lean_dec_ref(v_ext_1255_);
goto v___jp_1261_;
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec(v_declName_1257_);
lean_dec_ref(v_ext_1255_);
lean_dec(v_attrName_1254_);
v_a_1320_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1267_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1267_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
else
{
lean_dec_ref(v_ext_1255_);
goto v___jp_1261_;
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec(v_declName_1257_);
lean_dec_ref(v_ext_1255_);
lean_dec(v_attrName_1254_);
v_a_1328_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1264_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1264_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
v___jp_1261_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(v_attrName_1254_);
v___x_1263_ = l_Lean_Attribute_erase(v_declName_1257_, v___x_1262_, v___y_1258_, v___y_1259_);
return v___x_1263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__2___boxed(lean_object* v_attrName_1336_, lean_object* v_ext_1337_, lean_object* v___x_1338_, lean_object* v_declName_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lean_Meta_mkSimpAttr___lam__2(v_attrName_1336_, v_ext_1337_, v___x_1338_, v_declName_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec_ref(v___x_1338_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr(lean_object* v_attrName_1344_, lean_object* v_attrDescr_1345_, lean_object* v_ext_1346_, lean_object* v_ref_1347_){
_start:
{
lean_object* v___x_1349_; lean_object* v___f_1350_; lean_object* v___x_1351_; lean_object* v___f_1352_; lean_object* v___x_1353_; 
v___x_1349_ = lean_box(1);
lean_inc_ref(v_ext_1346_);
lean_inc_n(v_attrName_1344_, 3);
v___f_1350_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1350_, 0, v_attrName_1344_);
lean_closure_set(v___f_1350_, 1, v___x_1349_);
lean_closure_set(v___f_1350_, 2, v_ext_1346_);
v___x_1351_ = l_Lean_Meta_instInhabitedSimpTheorems_default;
v___f_1352_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lam__2___boxed), 7, 3);
lean_closure_set(v___f_1352_, 0, v_attrName_1344_);
lean_closure_set(v___f_1352_, 1, v_ext_1346_);
lean_closure_set(v___f_1352_, 2, v___x_1351_);
v___x_1353_ = l_Lean_registerAutomationAttr(v_attrName_1344_);
if (lean_obj_tag(v___x_1353_) == 0)
{
uint8_t v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_dec_ref_known(v___x_1353_, 1);
v___x_1354_ = 1;
v___x_1355_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1355_, 0, v_ref_1347_);
lean_ctor_set(v___x_1355_, 1, v_attrName_1344_);
lean_ctor_set(v___x_1355_, 2, v_attrDescr_1345_);
lean_ctor_set_uint8(v___x_1355_, sizeof(void*)*3, v___x_1354_);
v___x_1356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
lean_ctor_set(v___x_1356_, 1, v___f_1350_);
lean_ctor_set(v___x_1356_, 2, v___f_1352_);
v___x_1357_ = l_Lean_registerBuiltinAttribute(v___x_1356_);
return v___x_1357_;
}
else
{
lean_dec_ref(v___f_1352_);
lean_dec_ref(v___f_1350_);
lean_dec(v_ref_1347_);
lean_dec_ref(v_attrDescr_1345_);
lean_dec(v_attrName_1344_);
return v___x_1353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___boxed(lean_object* v_attrName_1358_, lean_object* v_attrDescr_1359_, lean_object* v_ext_1360_, lean_object* v_ref_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_Meta_mkSimpAttr(v_attrName_1358_, v_attrDescr_1359_, v_ext_1360_, v_ref_1361_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0(lean_object* v_00_u03b1_1364_, lean_object* v_constName_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(v_constName_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1372_, lean_object* v_constName_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0(v_00_u03b1_1372_, v_constName_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
return v_res_1379_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3(lean_object* v_00_u03b2_1380_, lean_object* v_x_1381_, lean_object* v_x_1382_){
_start:
{
uint8_t v___x_1383_; 
v___x_1383_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___redArg(v_x_1381_, v_x_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1384_, lean_object* v_x_1385_, lean_object* v_x_1386_){
_start:
{
uint8_t v_res_1387_; lean_object* v_r_1388_; 
v_res_1387_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3(v_00_u03b2_1384_, v_x_1385_, v_x_1386_);
lean_dec(v_x_1386_);
lean_dec_ref(v_x_1385_);
v_r_1388_ = lean_box(v_res_1387_);
return v_r_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1389_, lean_object* v_ref_1390_, lean_object* v_constName_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(v_ref_1390_, v_constName_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1398_, lean_object* v_ref_1399_, lean_object* v_constName_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1(v_00_u03b1_1398_, v_ref_1399_, v_constName_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v_ref_1399_);
return v_res_1406_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_1407_, lean_object* v_x_1408_, size_t v_x_1409_, lean_object* v_x_1410_){
_start:
{
uint8_t v___x_1411_; 
v___x_1411_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___redArg(v_x_1408_, v_x_1409_, v_x_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_1412_, lean_object* v_x_1413_, lean_object* v_x_1414_, lean_object* v_x_1415_){
_start:
{
size_t v_x_10153__boxed_1416_; uint8_t v_res_1417_; lean_object* v_r_1418_; 
v_x_10153__boxed_1416_ = lean_unbox_usize(v_x_1414_);
lean_dec(v_x_1414_);
v_res_1417_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6(v_00_u03b2_1412_, v_x_1413_, v_x_10153__boxed_1416_, v_x_1415_);
lean_dec(v_x_1415_);
lean_dec_ref(v_x_1413_);
v_r_1418_ = lean_box(v_res_1417_);
return v_r_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_1419_, lean_object* v_ref_1420_, lean_object* v_msg_1421_, lean_object* v_declHint_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_1420_, v_msg_1421_, v_declHint_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1429_, lean_object* v_ref_1430_, lean_object* v_msg_1431_, lean_object* v_declHint_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_1429_, v_ref_1430_, v_msg_1431_, v_declHint_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v_ref_1430_);
return v_res_1438_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_1439_, lean_object* v_keys_1440_, lean_object* v_vals_1441_, lean_object* v_heq_1442_, lean_object* v_i_1443_, lean_object* v_k_1444_){
_start:
{
uint8_t v___x_1445_; 
v___x_1445_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___redArg(v_keys_1440_, v_i_1443_, v_k_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_1446_, lean_object* v_keys_1447_, lean_object* v_vals_1448_, lean_object* v_heq_1449_, lean_object* v_i_1450_, lean_object* v_k_1451_){
_start:
{
uint8_t v_res_1452_; lean_object* v_r_1453_; 
v_res_1452_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__1_spec__3_spec__6_spec__9(v_00_u03b2_1446_, v_keys_1447_, v_vals_1448_, v_heq_1449_, v_i_1450_, v_k_1451_);
lean_dec(v_k_1451_);
lean_dec_ref(v_vals_1448_);
lean_dec_ref(v_keys_1447_);
v_r_1453_ = lean_box(v_res_1452_);
return v_r_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9(lean_object* v_msg_1454_, lean_object* v_declHint_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___redArg(v_msg_1454_, v_declHint_1455_, v___y_1459_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9___boxed(lean_object* v_msg_1462_, lean_object* v_declHint_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__6_spec__9(v_msg_1462_, v_declHint_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b1_1470_, lean_object* v_ref_1471_, lean_object* v_msg_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ref_1471_, v_msg_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b1_1479_, lean_object* v_ref_1480_, lean_object* v_msg_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b1_1479_, v_ref_1480_, v_msg_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v_ref_1480_);
return v_res_1487_;
}
}
static lean_object* _init_l_Lean_Meta_registerSimpAttr___auto__1(void){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__28, &l_Lean_Meta_mkSimpAttr___auto__1___closed__28_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__28);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2___redArg(lean_object* v_a_1489_, lean_object* v_b_1490_, lean_object* v_x_1491_){
_start:
{
if (lean_obj_tag(v_x_1491_) == 0)
{
lean_dec(v_b_1490_);
lean_dec(v_a_1489_);
return v_x_1491_;
}
else
{
lean_object* v_key_1492_; lean_object* v_value_1493_; lean_object* v_tail_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1506_; 
v_key_1492_ = lean_ctor_get(v_x_1491_, 0);
v_value_1493_ = lean_ctor_get(v_x_1491_, 1);
v_tail_1494_ = lean_ctor_get(v_x_1491_, 2);
v_isSharedCheck_1506_ = !lean_is_exclusive(v_x_1491_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1496_ = v_x_1491_;
v_isShared_1497_ = v_isSharedCheck_1506_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_tail_1494_);
lean_inc(v_value_1493_);
lean_inc(v_key_1492_);
lean_dec(v_x_1491_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1506_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
uint8_t v___x_1498_; 
v___x_1498_ = lean_name_eq(v_key_1492_, v_a_1489_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; lean_object* v___x_1501_; 
v___x_1499_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2___redArg(v_a_1489_, v_b_1490_, v_tail_1494_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 2, v___x_1499_);
v___x_1501_ = v___x_1496_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_key_1492_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_value_1493_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
else
{
lean_object* v___x_1504_; 
lean_dec(v_value_1493_);
lean_dec(v_key_1492_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 1, v_b_1490_);
lean_ctor_set(v___x_1496_, 0, v_a_1489_);
v___x_1504_ = v___x_1496_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1489_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v_b_1490_);
lean_ctor_set(v_reuseFailAlloc_1505_, 2, v_tail_1494_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1507_, lean_object* v_x_1508_){
_start:
{
if (lean_obj_tag(v_x_1508_) == 0)
{
return v_x_1507_;
}
else
{
lean_object* v_key_1509_; lean_object* v_value_1510_; lean_object* v_tail_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1537_; 
v_key_1509_ = lean_ctor_get(v_x_1508_, 0);
v_value_1510_ = lean_ctor_get(v_x_1508_, 1);
v_tail_1511_ = lean_ctor_get(v_x_1508_, 2);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_x_1508_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1513_ = v_x_1508_;
v_isShared_1514_ = v_isSharedCheck_1537_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_tail_1511_);
lean_inc(v_value_1510_);
lean_inc(v_key_1509_);
lean_dec(v_x_1508_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1537_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1515_; uint64_t v___y_1517_; 
v___x_1515_ = lean_array_get_size(v_x_1507_);
if (lean_obj_tag(v_key_1509_) == 0)
{
uint64_t v___x_1535_; 
v___x_1535_ = 1723ULL;
v___y_1517_ = v___x_1535_;
goto v___jp_1516_;
}
else
{
uint64_t v_hash_1536_; 
v_hash_1536_ = lean_ctor_get_uint64(v_key_1509_, sizeof(void*)*2);
v___y_1517_ = v_hash_1536_;
goto v___jp_1516_;
}
v___jp_1516_:
{
uint64_t v___x_1518_; uint64_t v___x_1519_; uint64_t v_fold_1520_; uint64_t v___x_1521_; uint64_t v___x_1522_; uint64_t v___x_1523_; size_t v___x_1524_; size_t v___x_1525_; size_t v___x_1526_; size_t v___x_1527_; size_t v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1531_; 
v___x_1518_ = 32ULL;
v___x_1519_ = lean_uint64_shift_right(v___y_1517_, v___x_1518_);
v_fold_1520_ = lean_uint64_xor(v___y_1517_, v___x_1519_);
v___x_1521_ = 16ULL;
v___x_1522_ = lean_uint64_shift_right(v_fold_1520_, v___x_1521_);
v___x_1523_ = lean_uint64_xor(v_fold_1520_, v___x_1522_);
v___x_1524_ = lean_uint64_to_usize(v___x_1523_);
v___x_1525_ = lean_usize_of_nat(v___x_1515_);
v___x_1526_ = ((size_t)1ULL);
v___x_1527_ = lean_usize_sub(v___x_1525_, v___x_1526_);
v___x_1528_ = lean_usize_land(v___x_1524_, v___x_1527_);
v___x_1529_ = lean_array_uget_borrowed(v_x_1507_, v___x_1528_);
lean_inc(v___x_1529_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 2, v___x_1529_);
v___x_1531_ = v___x_1513_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_key_1509_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_value_1510_);
lean_ctor_set(v_reuseFailAlloc_1534_, 2, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_array_uset(v_x_1507_, v___x_1528_, v___x_1531_);
v_x_1507_ = v___x_1532_;
v_x_1508_ = v_tail_1511_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1538_, lean_object* v_source_1539_, lean_object* v_target_1540_){
_start:
{
lean_object* v___x_1541_; uint8_t v___x_1542_; 
v___x_1541_ = lean_array_get_size(v_source_1539_);
v___x_1542_ = lean_nat_dec_lt(v_i_1538_, v___x_1541_);
if (v___x_1542_ == 0)
{
lean_dec_ref(v_source_1539_);
lean_dec(v_i_1538_);
return v_target_1540_;
}
else
{
lean_object* v_es_1543_; lean_object* v___x_1544_; lean_object* v_source_1545_; lean_object* v_target_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v_es_1543_ = lean_array_fget(v_source_1539_, v_i_1538_);
v___x_1544_ = lean_box(0);
v_source_1545_ = lean_array_fset(v_source_1539_, v_i_1538_, v___x_1544_);
v_target_1546_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1540_, v_es_1543_);
v___x_1547_ = lean_unsigned_to_nat(1u);
v___x_1548_ = lean_nat_add(v_i_1538_, v___x_1547_);
lean_dec(v_i_1538_);
v_i_1538_ = v___x_1548_;
v_source_1539_ = v_source_1545_;
v_target_1540_ = v_target_1546_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1___redArg(lean_object* v_data_1550_){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v_nbuckets_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1551_ = lean_array_get_size(v_data_1550_);
v___x_1552_ = lean_unsigned_to_nat(2u);
v_nbuckets_1553_ = lean_nat_mul(v___x_1551_, v___x_1552_);
v___x_1554_ = lean_unsigned_to_nat(0u);
v___x_1555_ = lean_box(0);
v___x_1556_ = lean_mk_array(v_nbuckets_1553_, v___x_1555_);
v___x_1557_ = lean_array_propagate_mark(v_data_1550_, v___x_1556_);
v___x_1558_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2___redArg(v___x_1554_, v_data_1550_, v___x_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(lean_object* v_a_1559_, lean_object* v_x_1560_){
_start:
{
if (lean_obj_tag(v_x_1560_) == 0)
{
uint8_t v___x_1561_; 
v___x_1561_ = 0;
return v___x_1561_;
}
else
{
lean_object* v_key_1562_; lean_object* v_tail_1563_; uint8_t v___x_1564_; 
v_key_1562_ = lean_ctor_get(v_x_1560_, 0);
v_tail_1563_ = lean_ctor_get(v_x_1560_, 2);
v___x_1564_ = lean_name_eq(v_key_1562_, v_a_1559_);
if (v___x_1564_ == 0)
{
v_x_1560_ = v_tail_1563_;
goto _start;
}
else
{
return v___x_1564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_1566_, lean_object* v_x_1567_){
_start:
{
uint8_t v_res_1568_; lean_object* v_r_1569_; 
v_res_1568_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(v_a_1566_, v_x_1567_);
lean_dec(v_x_1567_);
lean_dec(v_a_1566_);
v_r_1569_ = lean_box(v_res_1568_);
return v_r_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0___redArg(lean_object* v_m_1570_, lean_object* v_a_1571_, lean_object* v_b_1572_){
_start:
{
lean_object* v_size_1573_; lean_object* v_buckets_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1620_; 
v_size_1573_ = lean_ctor_get(v_m_1570_, 0);
v_buckets_1574_ = lean_ctor_get(v_m_1570_, 1);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_m_1570_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1576_ = v_m_1570_;
v_isShared_1577_ = v_isSharedCheck_1620_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_buckets_1574_);
lean_inc(v_size_1573_);
lean_dec(v_m_1570_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1620_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; uint64_t v___y_1580_; 
v___x_1578_ = lean_array_get_size(v_buckets_1574_);
if (lean_obj_tag(v_a_1571_) == 0)
{
uint64_t v___x_1618_; 
v___x_1618_ = 1723ULL;
v___y_1580_ = v___x_1618_;
goto v___jp_1579_;
}
else
{
uint64_t v_hash_1619_; 
v_hash_1619_ = lean_ctor_get_uint64(v_a_1571_, sizeof(void*)*2);
v___y_1580_ = v_hash_1619_;
goto v___jp_1579_;
}
v___jp_1579_:
{
uint64_t v___x_1581_; uint64_t v___x_1582_; uint64_t v_fold_1583_; uint64_t v___x_1584_; uint64_t v___x_1585_; uint64_t v___x_1586_; size_t v___x_1587_; size_t v___x_1588_; size_t v___x_1589_; size_t v___x_1590_; size_t v___x_1591_; lean_object* v_bkt_1592_; uint8_t v___x_1593_; 
v___x_1581_ = 32ULL;
v___x_1582_ = lean_uint64_shift_right(v___y_1580_, v___x_1581_);
v_fold_1583_ = lean_uint64_xor(v___y_1580_, v___x_1582_);
v___x_1584_ = 16ULL;
v___x_1585_ = lean_uint64_shift_right(v_fold_1583_, v___x_1584_);
v___x_1586_ = lean_uint64_xor(v_fold_1583_, v___x_1585_);
v___x_1587_ = lean_uint64_to_usize(v___x_1586_);
v___x_1588_ = lean_usize_of_nat(v___x_1578_);
v___x_1589_ = ((size_t)1ULL);
v___x_1590_ = lean_usize_sub(v___x_1588_, v___x_1589_);
v___x_1591_ = lean_usize_land(v___x_1587_, v___x_1590_);
v_bkt_1592_ = lean_array_uget_borrowed(v_buckets_1574_, v___x_1591_);
v___x_1593_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(v_a_1571_, v_bkt_1592_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; lean_object* v_size_x27_1595_; lean_object* v___x_1596_; lean_object* v_buckets_x27_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
v___x_1594_ = lean_unsigned_to_nat(1u);
v_size_x27_1595_ = lean_nat_add(v_size_1573_, v___x_1594_);
lean_dec(v_size_1573_);
lean_inc(v_bkt_1592_);
v___x_1596_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1596_, 0, v_a_1571_);
lean_ctor_set(v___x_1596_, 1, v_b_1572_);
lean_ctor_set(v___x_1596_, 2, v_bkt_1592_);
v_buckets_x27_1597_ = lean_array_uset(v_buckets_1574_, v___x_1591_, v___x_1596_);
v___x_1598_ = lean_unsigned_to_nat(4u);
v___x_1599_ = lean_nat_mul(v_size_x27_1595_, v___x_1598_);
v___x_1600_ = lean_unsigned_to_nat(3u);
v___x_1601_ = lean_nat_div(v___x_1599_, v___x_1600_);
lean_dec(v___x_1599_);
v___x_1602_ = lean_array_get_size(v_buckets_x27_1597_);
v___x_1603_ = lean_nat_dec_le(v___x_1601_, v___x_1602_);
lean_dec(v___x_1601_);
if (v___x_1603_ == 0)
{
lean_object* v_val_1604_; lean_object* v___x_1606_; 
v_val_1604_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1___redArg(v_buckets_x27_1597_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 1, v_val_1604_);
lean_ctor_set(v___x_1576_, 0, v_size_x27_1595_);
v___x_1606_ = v___x_1576_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_size_x27_1595_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_val_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
else
{
lean_object* v___x_1609_; 
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 1, v_buckets_x27_1597_);
lean_ctor_set(v___x_1576_, 0, v_size_x27_1595_);
v___x_1609_ = v___x_1576_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_size_x27_1595_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_buckets_x27_1597_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
else
{
lean_object* v___x_1611_; lean_object* v_buckets_x27_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1616_; 
lean_inc(v_bkt_1592_);
v___x_1611_ = lean_box(0);
v_buckets_x27_1612_ = lean_array_uset(v_buckets_1574_, v___x_1591_, v___x_1611_);
v___x_1613_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2___redArg(v_a_1571_, v_b_1572_, v_bkt_1592_);
v___x_1614_ = lean_array_uset(v_buckets_x27_1612_, v___x_1591_, v___x_1613_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 1, v___x_1614_);
v___x_1616_ = v___x_1576_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_size_1573_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v___x_1614_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerSimpAttr(lean_object* v_attrName_1621_, lean_object* v_attrDescr_1622_, lean_object* v_ref_1623_){
_start:
{
lean_object* v___x_1625_; 
lean_inc(v_ref_1623_);
v___x_1625_ = l_Lean_Meta_mkSimpExt(v_ref_1623_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1627_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc_n(v_a_1626_, 2);
lean_dec_ref_known(v___x_1625_, 1);
lean_inc(v_attrName_1621_);
v___x_1627_ = l_Lean_Meta_mkSimpAttr(v_attrName_1621_, v_attrDescr_1622_, v_a_1626_, v_ref_1623_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1638_; 
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1638_ == 0)
{
lean_object* v_unused_1639_; 
v_unused_1639_ = lean_ctor_get(v___x_1627_, 0);
lean_dec(v_unused_1639_);
v___x_1629_ = v___x_1627_;
v_isShared_1630_ = v_isSharedCheck_1638_;
goto v_resetjp_1628_;
}
else
{
lean_dec(v___x_1627_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1638_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1636_; 
v___x_1631_ = l_Lean_Meta_simpExtensionMapRef;
v___x_1632_ = lean_st_ref_take(v___x_1631_);
lean_inc(v_a_1626_);
v___x_1633_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0___redArg(v___x_1632_, v_attrName_1621_, v_a_1626_);
v___x_1634_ = lean_st_ref_put(v___x_1631_, v___x_1633_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v_a_1626_);
v___x_1636_ = v___x_1629_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1626_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec(v_a_1626_);
lean_dec(v_attrName_1621_);
v_a_1640_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1627_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1627_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
else
{
lean_dec(v_ref_1623_);
lean_dec_ref(v_attrDescr_1622_);
lean_dec(v_attrName_1621_);
return v___x_1625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerSimpAttr___boxed(lean_object* v_attrName_1648_, lean_object* v_attrDescr_1649_, lean_object* v_ref_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lean_Meta_registerSimpAttr(v_attrName_1648_, v_attrDescr_1649_, v_ref_1650_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0(lean_object* v_00_u03b2_1653_, lean_object* v_m_1654_, lean_object* v_a_1655_, lean_object* v_b_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0___redArg(v_m_1654_, v_a_1655_, v_b_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0(lean_object* v_00_u03b2_1658_, lean_object* v_a_1659_, lean_object* v_x_1660_){
_start:
{
uint8_t v___x_1661_; 
v___x_1661_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(v_a_1659_, v_x_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1662_, lean_object* v_a_1663_, lean_object* v_x_1664_){
_start:
{
uint8_t v_res_1665_; lean_object* v_r_1666_; 
v_res_1665_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0(v_00_u03b2_1662_, v_a_1663_, v_x_1664_);
lean_dec(v_x_1664_);
lean_dec(v_a_1663_);
v_r_1666_ = lean_box(v_res_1665_);
return v_r_1666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1(lean_object* v_00_u03b2_1667_, lean_object* v_data_1668_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1___redArg(v_data_1668_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2(lean_object* v_00_u03b2_1670_, lean_object* v_a_1671_, lean_object* v_b_1672_, lean_object* v_x_1673_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2___redArg(v_a_1671_, v_b_1672_, v_x_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1675_, lean_object* v_i_1676_, lean_object* v_source_1677_, lean_object* v_target_1678_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2___redArg(v_i_1676_, v_source_1677_, v_target_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1680_, lean_object* v_x_1681_, lean_object* v_x_1682_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1681_, v_x_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1695_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_));
v___x_1696_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_));
v___x_1697_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_));
v___x_1698_ = l_Lean_Meta_registerSimpAttr(v___x_1695_, v___x_1696_, v___x_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2____boxed(lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_();
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1711_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_));
v___x_1712_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_));
v___x_1713_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_));
v___x_1714_ = l_Lean_Meta_registerSimpAttr(v___x_1711_, v___x_1712_, v___x_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2____boxed(lean_object* v_a_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_();
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___redArg(lean_object* v_a_1717_){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = l_Lean_Meta_simpExtension;
v___x_1720_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_1719_, v_a_1717_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___redArg___boxed(lean_object* v_a_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_1721_);
lean_dec(v_a_1721_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems(lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_Meta_getSimpTheorems(v_a_1728_, v_a_1729_);
lean_dec(v_a_1729_);
lean_dec_ref(v_a_1728_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___redArg(lean_object* v_a_1732_){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = l_Lean_Meta_sevalSimpExtension;
v___x_1735_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_1734_, v_a_1732_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___redArg___boxed(lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Meta_getSEvalTheorems___redArg(v_a_1736_);
lean_dec(v_a_1736_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems(lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_Meta_getSEvalTheorems___redArg(v_a_1740_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___boxed(lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_Meta_getSEvalTheorems(v_a_1743_, v_a_1744_);
lean_dec(v_a_1744_);
lean_dec_ref(v_a_1743_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___redArg(lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_1756_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1760_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1758_, 1);
v___x_1760_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1756_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1761_);
lean_dec_ref_known(v___x_1760_, 1);
v___x_1762_ = ((lean_object*)(l_Lean_Meta_Simp_Context_mkDefault___redArg___closed__0));
v___x_1763_ = lean_unsigned_to_nat(1u);
v___x_1764_ = lean_mk_empty_array_with_capacity(v___x_1763_);
v___x_1765_ = lean_array_push(v___x_1764_, v_a_1759_);
v___x_1766_ = l_Lean_Options_empty;
v___x_1767_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1762_, v___x_1765_, v_a_1761_, v___x_1766_, v_a_1754_, v_a_1755_, v_a_1756_);
return v___x_1767_;
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_dec(v_a_1759_);
v_a_1768_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1760_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1760_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
v_a_1776_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1758_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1758_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___redArg___boxed(lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_Meta_Simp_Context_mkDefault___redArg(v_a_1784_, v_a_1785_, v_a_1786_);
lean_dec(v_a_1786_);
lean_dec_ref(v_a_1785_);
lean_dec_ref(v_a_1784_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault(lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Lean_Meta_Simp_Context_mkDefault___redArg(v_a_1789_, v_a_1791_, v_a_1792_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___boxed(lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_Meta_Simp_Context_mkDefault(v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
lean_dec(v_a_1798_);
lean_dec_ref(v_a_1797_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
return v_res_1800_;
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
