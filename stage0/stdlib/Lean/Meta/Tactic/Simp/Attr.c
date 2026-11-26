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
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_instBEqConstantKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSimpExt(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Simp_isSimproc___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_isBuiltinSimproc___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Meta_isSimpTheoremFromConstGuardedBy(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(lean_object*);
lean_object* l_Lean_Attribute_add(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_getAttrParamOptPrio(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lean_getOriginalConstKind_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_ignoreEquations(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_Simp_unfoldEvenWithEqns___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_registerAutomationAttr(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__18;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__19 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__19_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__20;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__21 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__21_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__22;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__23 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__23_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__24;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__25 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__25_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__26;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 1, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_mkSimpAttr___lam__0___closed__1;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__2;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__3;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__4;
static const lean_array_object l_Lean_Meta_mkSimpAttr___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__6;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__7;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__8;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__9;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__0___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkSimpAttr___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Cannot add `simp` attribute to `"};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__1___closed__1;
static const lean_string_object l_Lean_Meta_mkSimpAttr___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`: It is not a proposition nor a definition (to unfold)"};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__1___closed__3;
static const lean_string_object l_Lean_Meta_mkSimpAttr___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 165, .m_capacity = 165, .m_length = 164, .m_data = "The `[simp]` attribute can be added to lemmas that should be automatically used by the simplifier and to definitions that the simplifier should automatically unfold"};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__1___closed__5;
static lean_once_cell_t l_Lean_Meta_mkSimpAttr___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSimpAttr___lam__1___closed__6;
static const lean_string_object l_Lean_Meta_mkSimpAttr___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpPost"};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__1___closed__7 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__1___closed__7_value;
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___lam__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___lam__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___lam__1___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___lam__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___lam__1___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_mkSimpAttr___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_mkSimpAttr___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSimpAttr___lam__1___closed__8_value_aux_2),((lean_object*)&l_Lean_Meta_mkSimpAttr___lam__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(38, 218, 35, 149, 208, 200, 230, 161)}};
static const lean_object* l_Lean_Meta_mkSimpAttr___lam__1___closed__8 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___lam__1___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7_spec__12___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "` does not have the `[simp]` attribute"};
static const lean_object* l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2___closed__0 = (const lean_object*)&l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2___closed__0_value;
static lean_once_cell_t l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_mkSimpAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_mkSimpAttr___lam__0___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Meta_mkSimpAttr___closed__0 = (const lean_object*)&l_Lean_Meta_mkSimpAttr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_85_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v___x_83_);
lean_ctor_set(v___x_85_, 2, v___x_82_);
lean_ctor_set(v___x_85_, 3, v___x_83_);
lean_ctor_set(v___x_85_, 4, v___x_83_);
lean_ctor_set(v___x_85_, 5, v___x_83_);
lean_ctor_set(v___x_85_, 6, v___x_81_);
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
uint8_t v_post_boxed_178_; uint8_t v_a_4000__boxed_179_; uint8_t v_attrKind_boxed_180_; size_t v_sz_boxed_181_; size_t v_i_boxed_182_; lean_object* v_res_183_; 
v_post_boxed_178_ = lean_unbox(v_post_165_);
v_a_4000__boxed_179_ = lean_unbox(v_a_166_);
v_attrKind_boxed_180_ = lean_unbox(v_attrKind_167_);
v_sz_boxed_181_ = lean_unbox_usize(v_sz_170_);
lean_dec(v_sz_170_);
v_i_boxed_182_ = lean_unbox_usize(v_i_171_);
lean_dec(v_i_171_);
v_res_183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addDeclToUnfold_spec__1(v_ext_164_, v_post_boxed_178_, v_a_4000__boxed_179_, v_attrKind_boxed_180_, v_prio_168_, v_as_169_, v_sz_boxed_181_, v_i_boxed_182_, v_b_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__8___redArg(lean_object* v_ref_467_, lean_object* v_msg_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v_toCold_474_; lean_object* v_currRecDepth_475_; lean_object* v_ref_476_; uint16_t v_optionFlags_477_; uint8_t v_suppressElabErrors_478_; uint8_t v_checkDeprecated_479_; uint8_t v_isRecordingDeps_480_; lean_object* v_ref_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_toCold_474_ = lean_ctor_get(v___y_471_, 0);
v_currRecDepth_475_ = lean_ctor_get(v___y_471_, 1);
v_ref_476_ = lean_ctor_get(v___y_471_, 2);
v_optionFlags_477_ = lean_ctor_get_uint16(v___y_471_, sizeof(void*)*3);
v_suppressElabErrors_478_ = lean_ctor_get_uint8(v___y_471_, sizeof(void*)*3 + 2);
v_checkDeprecated_479_ = lean_ctor_get_uint8(v___y_471_, sizeof(void*)*3 + 3);
v_isRecordingDeps_480_ = lean_ctor_get_uint8(v___y_471_, sizeof(void*)*3 + 4);
v_ref_481_ = l_Lean_replaceRef(v_ref_467_, v_ref_476_);
lean_inc(v_currRecDepth_475_);
lean_inc_ref(v_toCold_474_);
v___x_482_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_482_, 0, v_toCold_474_);
lean_ctor_set(v___x_482_, 1, v_currRecDepth_475_);
lean_ctor_set(v___x_482_, 2, v_ref_481_);
lean_ctor_set_uint16(v___x_482_, sizeof(void*)*3, v_optionFlags_477_);
lean_ctor_set_uint8(v___x_482_, sizeof(void*)*3 + 2, v_suppressElabErrors_478_);
lean_ctor_set_uint8(v___x_482_, sizeof(void*)*3 + 3, v_checkDeprecated_479_);
lean_ctor_set_uint8(v___x_482_, sizeof(void*)*3 + 4, v_isRecordingDeps_480_);
v___x_483_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(v_msg_468_, v___y_469_, v___y_470_, v___x_482_, v___y_472_);
lean_dec_ref_known(v___x_482_, 3);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_ref_484_, lean_object* v_msg_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__8___redArg(v_ref_484_, v_msg_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v_ref_484_);
return v_res_491_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__0);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_494_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__0);
v___x_495_ = lean_unsigned_to_nat(0u);
v___x_496_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
lean_ctor_set(v___x_496_, 2, v___x_495_);
lean_ctor_set(v___x_496_, 3, v___x_495_);
lean_ctor_set(v___x_496_, 4, v___x_494_);
lean_ctor_set(v___x_496_, 5, v___x_494_);
lean_ctor_set(v___x_496_, 6, v___x_494_);
lean_ctor_set(v___x_496_, 7, v___x_494_);
lean_ctor_set(v___x_496_, 8, v___x_494_);
lean_ctor_set(v___x_496_, 9, v___x_494_);
lean_ctor_set(v___x_496_, 10, v___x_494_);
return v___x_496_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_497_ = lean_unsigned_to_nat(32u);
v___x_498_ = lean_mk_empty_array_with_capacity(v___x_497_);
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__3(void){
_start:
{
size_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_500_ = ((size_t)5ULL);
v___x_501_ = lean_unsigned_to_nat(0u);
v___x_502_ = lean_unsigned_to_nat(32u);
v___x_503_ = lean_mk_empty_array_with_capacity(v___x_502_);
v___x_504_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__2);
v___x_505_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_505_, 0, v___x_504_);
lean_ctor_set(v___x_505_, 1, v___x_503_);
lean_ctor_set(v___x_505_, 2, v___x_501_);
lean_ctor_set(v___x_505_, 3, v___x_501_);
lean_ctor_set_usize(v___x_505_, 4, v___x_500_);
return v___x_505_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_506_ = lean_box(1);
v___x_507_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__3);
v___x_508_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__0);
v___x_509_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v___x_507_);
lean_ctor_set(v___x_509_, 2, v___x_506_);
return v___x_509_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__6(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__5));
v___x_512_ = l_Lean_stringToMessageData(v___x_511_);
return v___x_512_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__8(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__7));
v___x_515_ = l_Lean_stringToMessageData(v___x_514_);
return v___x_515_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__10(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__9));
v___x_518_ = l_Lean_stringToMessageData(v___x_517_);
return v___x_518_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__12(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__11));
v___x_521_ = l_Lean_stringToMessageData(v___x_520_);
return v___x_521_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__14(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__13));
v___x_524_ = l_Lean_stringToMessageData(v___x_523_);
return v___x_524_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__16(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__15));
v___x_527_ = l_Lean_stringToMessageData(v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__18(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__17));
v___x_530_ = l_Lean_stringToMessageData(v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__20(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__19));
v___x_533_ = l_Lean_stringToMessageData(v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__22(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__21));
v___x_536_ = l_Lean_stringToMessageData(v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__24(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__23));
v___x_539_ = l_Lean_stringToMessageData(v___x_538_);
return v___x_539_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__26(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__25));
v___x_542_ = l_Lean_stringToMessageData(v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg(lean_object* v_msg_543_, lean_object* v_declHint_544_, lean_object* v___y_545_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v_env_549_; uint8_t v___x_550_; 
v___x_547_ = lean_box(0);
v___x_548_ = lean_st_ref_get(v___y_545_);
v_env_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc_ref(v_env_549_);
lean_dec(v___x_548_);
v___x_550_ = l_Lean_Name_isAnonymous(v_declHint_544_);
if (v___x_550_ == 0)
{
uint8_t v_isExporting_551_; 
v_isExporting_551_ = lean_ctor_get_uint8(v_env_549_, sizeof(void*)*13);
if (v_isExporting_551_ == 0)
{
lean_object* v___x_552_; 
lean_dec_ref(v_env_549_);
lean_dec(v_declHint_544_);
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v_msg_543_);
return v___x_552_;
}
else
{
lean_object* v___x_553_; uint8_t v___x_554_; 
lean_inc_ref(v_env_549_);
v___x_553_ = l_Lean_Environment_setExporting(v_env_549_, v___x_550_);
lean_inc(v_declHint_544_);
lean_inc_ref(v___x_553_);
v___x_554_ = l_Lean_Environment_contains(v___x_553_, v_declHint_544_, v_isExporting_551_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; 
lean_dec_ref(v___x_553_);
lean_dec_ref(v_env_549_);
lean_dec(v_declHint_544_);
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v_msg_543_);
return v___x_555_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v_c_561_; lean_object* v___x_562_; 
v___x_556_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__1);
v___x_557_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__4);
v___x_558_ = l_Lean_Options_empty;
lean_inc_ref(v___x_553_);
v___x_559_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_559_, 0, v___x_553_);
lean_ctor_set(v___x_559_, 1, v___x_556_);
lean_ctor_set(v___x_559_, 2, v___x_557_);
lean_ctor_set(v___x_559_, 3, v___x_558_);
lean_inc(v_declHint_544_);
v___x_560_ = l_Lean_MessageData_ofConstName(v_declHint_544_, v___x_550_);
v_c_561_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_561_, 0, v___x_559_);
lean_ctor_set(v_c_561_, 1, v___x_560_);
v___x_562_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_553_, v_declHint_544_);
lean_dec_ref(v___x_553_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
lean_dec_ref(v_env_549_);
lean_dec(v_declHint_544_);
v___x_563_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__6);
v___x_564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v_c_561_);
v___x_565_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__8);
v___x_566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_564_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
v___x_567_ = l_Lean_MessageData_note(v___x_566_);
v___x_568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_568_, 0, v_msg_543_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
else
{
lean_object* v_val_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_623_; 
v_val_570_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_623_ == 0)
{
v___x_572_ = v___x_562_;
v_isShared_573_ = v_isSharedCheck_623_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_val_570_);
lean_dec(v___x_562_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_623_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_574_; lean_object* v_modules_575_; lean_object* v_moduleNames_576_; lean_object* v_mod_577_; uint8_t v___x_592_; 
v___x_574_ = l_Lean_Environment_header(v_env_549_);
lean_dec_ref(v_env_549_);
v_modules_575_ = lean_ctor_get(v___x_574_, 3);
lean_inc_ref(v_modules_575_);
v_moduleNames_576_ = lean_ctor_get(v___x_574_, 4);
lean_inc_ref(v_moduleNames_576_);
lean_dec_ref(v___x_574_);
v_mod_577_ = lean_array_get(v___x_547_, v_moduleNames_576_, v_val_570_);
lean_dec_ref(v_moduleNames_576_);
v___x_592_ = l_Lean_isPrivateName(v_declHint_544_);
lean_dec(v_declHint_544_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_593_ = lean_array_get_size(v_modules_575_);
v___x_594_ = lean_nat_dec_lt(v_val_570_, v___x_593_);
if (v___x_594_ == 0)
{
lean_dec_ref(v_modules_575_);
lean_dec(v_val_570_);
goto v___jp_578_;
}
else
{
lean_object* v___x_595_; lean_object* v_toImport_596_; uint8_t v_isExported_597_; 
v___x_595_ = lean_array_fget(v_modules_575_, v_val_570_);
lean_dec(v_val_570_);
lean_dec_ref(v_modules_575_);
v_toImport_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc_ref(v_toImport_596_);
lean_dec(v___x_595_);
v_isExported_597_ = lean_ctor_get_uint8(v_toImport_596_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_596_);
if (v_isExported_597_ == 0)
{
goto v___jp_578_;
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
lean_del_object(v___x_572_);
v___x_598_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__16);
v___x_599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
lean_ctor_set(v___x_599_, 1, v_c_561_);
v___x_600_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__18);
v___x_601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = l_Lean_MessageData_ofName(v_mod_577_);
lean_inc_ref(v___x_602_);
v___x_603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__20);
v___x_605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_603_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v___x_602_);
v___x_607_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__22);
v___x_608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = l_Lean_MessageData_note(v___x_608_);
v___x_610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_610_, 0, v_msg_543_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
return v___x_611_;
}
}
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
lean_dec_ref(v_modules_575_);
lean_del_object(v___x_572_);
lean_dec(v_val_570_);
v___x_612_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__6);
v___x_613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v_c_561_);
v___x_614_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__24, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__24_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__24);
v___x_615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = l_Lean_MessageData_ofName(v_mod_577_);
v___x_617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__26, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__26_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__26);
v___x_619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = l_Lean_MessageData_note(v___x_619_);
v___x_621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_621_, 0, v_msg_543_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
return v___x_622_;
}
v___jp_578_:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_579_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__10);
v___x_580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v_c_561_);
v___x_581_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__12);
v___x_582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_580_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = l_Lean_MessageData_ofName(v_mod_577_);
v___x_584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_582_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__14);
v___x_586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = l_Lean_MessageData_note(v___x_586_);
v___x_588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_588_, 0, v_msg_543_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
if (v_isShared_573_ == 0)
{
lean_ctor_set_tag(v___x_572_, 0);
lean_ctor_set(v___x_572_, 0, v___x_588_);
v___x_590_ = v___x_572_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_624_; 
lean_dec_ref(v_env_549_);
lean_dec(v_declHint_544_);
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v_msg_543_);
return v___x_624_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_msg_625_, lean_object* v_declHint_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg(v_msg_625_, v_declHint_626_, v___y_627_);
lean_dec(v___y_627_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_msg_630_, lean_object* v_declHint_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v___x_637_; lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_647_; 
v___x_637_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg(v_msg_630_, v_declHint_631_, v___y_635_);
v_a_638_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_647_ == 0)
{
v___x_640_ = v___x_637_;
v_isShared_641_ = v_isSharedCheck_647_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_637_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_647_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_642_ = l_Lean_unknownIdentifierMessageTag;
v___x_643_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v_a_638_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_643_);
v___x_645_ = v___x_640_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_msg_648_, lean_object* v_declHint_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7(v_msg_648_, v_declHint_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_656_, lean_object* v_msg_657_, lean_object* v_declHint_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v___x_664_; lean_object* v_a_665_; lean_object* v___x_666_; 
v___x_664_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7(v_msg_657_, v_declHint_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref(v___x_664_);
v___x_666_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__8___redArg(v_ref_656_, v_a_665_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_667_, lean_object* v_msg_668_, lean_object* v_declHint_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_667_, v_msg_668_, v_declHint_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v_ref_667_);
return v_res_675_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_678_ = l_Lean_stringToMessageData(v___x_677_);
return v___x_678_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_681_ = l_Lean_stringToMessageData(v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_682_, lean_object* v_constName_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___x_689_; uint8_t v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_689_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_690_ = 0;
lean_inc(v_constName_683_);
v___x_691_ = l_Lean_MessageData_ofConstName(v_constName_683_, v___x_690_);
v___x_692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_689_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_692_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_682_, v___x_694_, v_constName_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_696_, lean_object* v_constName_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(v_ref_696_, v_constName_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v_ref_696_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(lean_object* v_constName_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_ref_710_; lean_object* v___x_711_; 
v_ref_710_ = lean_ctor_get(v___y_707_, 2);
v___x_711_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(v_ref_710_, v_constName_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg___boxed(lean_object* v_constName_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(v_constName_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0(lean_object* v_constName_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_725_; lean_object* v_env_726_; uint8_t v___x_727_; lean_object* v___x_728_; 
v___x_725_ = lean_st_ref_get(v___y_723_);
v_env_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc_ref(v_env_726_);
lean_dec(v___x_725_);
v___x_727_ = 0;
lean_inc(v_constName_719_);
v___x_728_ = l_Lean_Environment_find_x3f(v_env_726_, v_constName_719_, v___x_727_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(v_constName_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
return v___x_729_;
}
else
{
lean_object* v_val_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec(v_constName_719_);
v_val_730_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_728_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_val_730_);
lean_dec(v___x_728_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
lean_ctor_set_tag(v___x_732_, 0);
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_val_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0___boxed(lean_object* v_constName_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0(v_constName_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
return v_res_744_;
}
}
static uint64_t _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_751_; uint64_t v___x_752_; 
v___x_751_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__0));
v___x_752_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_751_);
return v___x_752_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__2(void){
_start:
{
uint64_t v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = lean_uint64_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__1, &l_Lean_Meta_mkSimpAttr___lam__0___closed__1_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__1);
v___x_754_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__0));
v___x_755_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set_uint64(v___x_755_, sizeof(void*)*1, v___x_753_);
return v___x_755_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__3(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2_spec__2_spec__3___redArg___closed__0);
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__4(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_758_ = lean_box(1);
v___x_759_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__3);
v___x_760_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__3, &l_Lean_Meta_mkSimpAttr___lam__0___closed__3_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__3);
v___x_761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
lean_ctor_set(v___x_761_, 1, v___x_759_);
lean_ctor_set(v___x_761_, 2, v___x_758_);
return v___x_761_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_764_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__3, &l_Lean_Meta_mkSimpAttr___lam__0___closed__3_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__3);
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
lean_ctor_set(v___x_766_, 2, v___x_765_);
lean_ctor_set(v___x_766_, 3, v___x_765_);
lean_ctor_set(v___x_766_, 4, v___x_764_);
lean_ctor_set(v___x_766_, 5, v___x_764_);
lean_ctor_set(v___x_766_, 6, v___x_764_);
lean_ctor_set(v___x_766_, 7, v___x_764_);
lean_ctor_set(v___x_766_, 8, v___x_764_);
lean_ctor_set(v___x_766_, 9, v___x_764_);
lean_ctor_set(v___x_766_, 10, v___x_764_);
return v___x_766_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__7(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__3, &l_Lean_Meta_mkSimpAttr___lam__0___closed__3_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__3);
v___x_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
return v___x_768_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__8(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__3, &l_Lean_Meta_mkSimpAttr___lam__0___closed__3_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__3);
v___x_771_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
lean_ctor_set(v___x_771_, 2, v___x_769_);
return v___x_771_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__9(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_772_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__8, &l_Lean_Meta_mkSimpAttr___lam__0___closed__8_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__8);
v___x_773_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__7, &l_Lean_Meta_mkSimpAttr___lam__0___closed__7_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__7);
v___x_774_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__3, &l_Lean_Meta_mkSimpAttr___lam__0___closed__3_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__3);
v___x_775_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__2);
v___x_776_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set(v___x_776_, 1, v___x_774_);
lean_ctor_set(v___x_776_, 2, v___x_773_);
lean_ctor_set(v___x_776_, 3, v___x_774_);
lean_ctor_set(v___x_776_, 4, v___x_774_);
lean_ctor_set(v___x_776_, 5, v___x_774_);
lean_ctor_set(v___x_776_, 6, v___x_772_);
return v___x_776_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__10(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__3, &l_Lean_Meta_mkSimpAttr___lam__0___closed__3_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__3);
v___x_778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
lean_ctor_set(v___x_778_, 2, v___x_777_);
lean_ctor_set(v___x_778_, 3, v___x_777_);
lean_ctor_set(v___x_778_, 4, v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__0(lean_object* v___x_779_, lean_object* v_p_780_, lean_object* v_declName_781_, lean_object* v_stx_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
uint8_t v___x_786_; uint8_t v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v_a_801_; lean_object* v___y_806_; lean_object* v___x_809_; 
v___x_786_ = 0;
v___x_787_ = 1;
v___x_788_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__2, &l_Lean_Meta_mkSimpAttr___lam__0___closed__2_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__2);
v___x_789_ = lean_unsigned_to_nat(0u);
v___x_790_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__3);
v___x_791_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__4, &l_Lean_Meta_mkSimpAttr___lam__0___closed__4_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__4);
v___x_792_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__5));
v___x_793_ = lean_box(0);
lean_inc(v___x_779_);
v___x_794_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_794_, 0, v___x_788_);
lean_ctor_set(v___x_794_, 1, v___x_779_);
lean_ctor_set(v___x_794_, 2, v___x_791_);
lean_ctor_set(v___x_794_, 3, v___x_792_);
lean_ctor_set(v___x_794_, 4, v___x_793_);
lean_ctor_set(v___x_794_, 5, v___x_789_);
lean_ctor_set(v___x_794_, 6, v___x_793_);
lean_ctor_set_uint8(v___x_794_, sizeof(void*)*7, v___x_786_);
lean_ctor_set_uint8(v___x_794_, sizeof(void*)*7 + 1, v___x_786_);
lean_ctor_set_uint8(v___x_794_, sizeof(void*)*7 + 2, v___x_786_);
lean_ctor_set_uint8(v___x_794_, sizeof(void*)*7 + 3, v___x_787_);
v___x_795_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__6, &l_Lean_Meta_mkSimpAttr___lam__0___closed__6_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__6);
v___x_796_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__9, &l_Lean_Meta_mkSimpAttr___lam__0___closed__9_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__9);
v___x_797_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__10, &l_Lean_Meta_mkSimpAttr___lam__0___closed__10_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__10);
v___x_798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_798_, 0, v___x_795_);
lean_ctor_set(v___x_798_, 1, v___x_796_);
lean_ctor_set(v___x_798_, 2, v___x_779_);
lean_ctor_set(v___x_798_, 3, v___x_790_);
lean_ctor_set(v___x_798_, 4, v___x_797_);
v___x_799_ = lean_st_mk_ref(v___x_798_);
lean_inc(v_declName_781_);
v___x_809_ = l_Lean_Meta_Simp_isSimproc___redArg(v_declName_781_, v___y_784_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; uint8_t v___x_811_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_810_);
lean_dec_ref_known(v___x_809_, 1);
v___x_811_ = lean_unbox(v_a_810_);
lean_dec(v_a_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_Meta_Simp_isBuiltinSimproc___redArg(v_declName_781_, v___y_784_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; uint8_t v___x_814_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
lean_dec_ref_known(v___x_812_, 1);
v___x_814_ = lean_unbox(v_a_813_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; 
lean_inc(v_declName_781_);
v___x_815_ = l_Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0(v_declName_781_, v___x_794_, v___x_799_, v___y_783_, v___y_784_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_a_816_);
lean_dec_ref_known(v___x_815_, 1);
v___x_817_ = l_Lean_ConstantInfo_type(v_a_816_);
lean_dec(v_a_816_);
v___x_818_ = l_Lean_Meta_isProp(v___x_817_, v___x_794_, v___x_799_, v___y_783_, v___y_784_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; uint8_t v___x_820_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_818_, 1);
v___x_820_ = lean_unbox(v_a_819_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; uint8_t v___x_822_; 
lean_dec(v_a_819_);
lean_dec(v_a_813_);
lean_dec_ref_known(v___x_794_, 7);
v___x_821_ = lean_apply_1(v_p_780_, v_declName_781_);
v___x_822_ = lean_unbox(v___x_821_);
v_a_801_ = v___x_822_;
goto v___jp_800_;
}
else
{
lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_823_ = lean_unsigned_to_nat(2u);
v___x_824_ = l_Lean_Syntax_getArg(v_stx_782_, v___x_823_);
v___x_825_ = l_Lean_Syntax_isNone(v___x_824_);
lean_dec(v___x_824_);
if (v___x_825_ == 0)
{
uint8_t v___x_826_; lean_object* v___x_827_; 
lean_dec(v_a_813_);
v___x_826_ = lean_unbox(v_a_819_);
lean_dec(v_a_819_);
v___x_827_ = l_Lean_Meta_isSimpTheoremFromConstGuardedBy(v_p_780_, v_declName_781_, v___x_826_, v___x_794_, v___x_799_, v___y_783_, v___y_784_);
lean_dec_ref_known(v___x_794_, 7);
v___y_806_ = v___x_827_;
goto v___jp_805_;
}
else
{
uint8_t v___x_828_; lean_object* v___x_829_; 
lean_dec(v_a_819_);
v___x_828_ = lean_unbox(v_a_813_);
lean_dec(v_a_813_);
v___x_829_ = l_Lean_Meta_isSimpTheoremFromConstGuardedBy(v_p_780_, v_declName_781_, v___x_828_, v___x_794_, v___x_799_, v___y_783_, v___y_784_);
lean_dec_ref_known(v___x_794_, 7);
v___y_806_ = v___x_829_;
goto v___jp_805_;
}
}
}
else
{
lean_dec(v_a_813_);
lean_dec(v___x_799_);
lean_dec_ref_known(v___x_794_, 7);
lean_dec(v_declName_781_);
lean_dec_ref(v_p_780_);
return v___x_818_;
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec(v_a_813_);
lean_dec(v___x_799_);
lean_dec_ref_known(v___x_794_, 7);
lean_dec(v_declName_781_);
lean_dec_ref(v_p_780_);
v_a_830_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_815_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_815_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
else
{
lean_dec(v_a_813_);
lean_dec_ref_known(v___x_794_, 7);
lean_dec(v_declName_781_);
lean_dec_ref(v_p_780_);
v_a_801_ = v___x_786_;
goto v___jp_800_;
}
}
else
{
lean_dec(v___x_799_);
lean_dec_ref_known(v___x_794_, 7);
lean_dec(v_declName_781_);
lean_dec_ref(v_p_780_);
return v___x_812_;
}
}
else
{
lean_dec_ref_known(v___x_794_, 7);
lean_dec(v_declName_781_);
lean_dec_ref(v_p_780_);
v_a_801_ = v___x_786_;
goto v___jp_800_;
}
}
else
{
lean_dec(v___x_799_);
lean_dec_ref_known(v___x_794_, 7);
lean_dec(v_declName_781_);
lean_dec_ref(v_p_780_);
return v___x_809_;
}
v___jp_800_:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_802_ = lean_st_ref_get(v___x_799_);
lean_dec(v___x_799_);
lean_dec(v___x_802_);
v___x_803_ = lean_box(v_a_801_);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
return v___x_804_;
}
v___jp_805_:
{
if (lean_obj_tag(v___y_806_) == 0)
{
lean_object* v_a_807_; uint8_t v___x_808_; 
v_a_807_ = lean_ctor_get(v___y_806_, 0);
lean_inc(v_a_807_);
lean_dec_ref_known(v___y_806_, 1);
v___x_808_ = lean_unbox(v_a_807_);
lean_dec(v_a_807_);
v_a_801_ = v___x_808_;
goto v___jp_800_;
}
else
{
lean_dec(v___x_799_);
return v___y_806_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__0___boxed(lean_object* v___x_838_, lean_object* v_p_839_, lean_object* v_declName_840_, lean_object* v_stx_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_Meta_mkSimpAttr___lam__0(v___x_838_, v_p_839_, v_declName_840_, v_stx_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v_stx_841_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__1(lean_object* v_constName_846_, uint8_t v_skipRealize_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v___x_853_; lean_object* v_env_854_; lean_object* v___x_855_; 
v___x_853_ = lean_st_ref_get(v___y_851_);
v_env_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc_ref(v_env_854_);
lean_dec(v___x_853_);
lean_inc(v_constName_846_);
v___x_855_ = l_Lean_Environment_findAsync_x3f(v_env_854_, v_constName_846_, v_skipRealize_847_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(v_constName_846_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
return v___x_856_;
}
else
{
lean_object* v_val_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
lean_dec(v_constName_846_);
v_val_857_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_855_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_val_857_);
lean_dec(v___x_855_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
lean_ctor_set_tag(v___x_859_, 0);
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_val_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__1___boxed(lean_object* v_constName_865_, lean_object* v_skipRealize_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
uint8_t v_skipRealize_boxed_872_; lean_object* v_res_873_; 
v_skipRealize_boxed_872_ = lean_unbox(v_skipRealize_866_);
v_res_873_ = l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__1(v_constName_865_, v_skipRealize_boxed_872_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
return v_res_873_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__1___closed__0));
v___x_876_ = l_Lean_stringToMessageData(v___x_875_);
return v___x_876_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__1___closed__2));
v___x_879_ = l_Lean_stringToMessageData(v___x_878_);
return v___x_879_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__1___closed__5(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__1___closed__4));
v___x_882_ = l_Lean_stringToMessageData(v___x_881_);
return v___x_882_;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lam__1___closed__6(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__1___closed__5, &l_Lean_Meta_mkSimpAttr___lam__1___closed__5_once, _init_l_Lean_Meta_mkSimpAttr___lam__1___closed__5);
v___x_884_ = l_Lean_MessageData_note(v___x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__1(lean_object* v_attrName_891_, lean_object* v___x_892_, lean_object* v_ext_893_, lean_object* v_declName_894_, lean_object* v_stx_895_, uint8_t v_attrKind_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v___x_903_; 
lean_inc(v_declName_894_);
v___x_903_ = l_Lean_Meta_Simp_isSimproc___redArg(v_declName_894_, v___y_898_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; uint8_t v___x_905_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_904_);
lean_dec_ref_known(v___x_903_, 1);
v___x_905_ = lean_unbox(v_a_904_);
lean_dec(v_a_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_Meta_Simp_isBuiltinSimproc___redArg(v_declName_894_, v___y_898_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_1022_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_1022_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_1022_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
uint8_t v___x_911_; 
v___x_911_ = lean_unbox(v_a_907_);
if (v___x_911_ == 0)
{
uint8_t v___x_912_; uint8_t v___x_913_; uint8_t v___x_914_; uint8_t v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; uint8_t v___x_918_; uint8_t v___x_919_; uint8_t v___x_920_; uint8_t v___x_921_; uint8_t v___x_922_; uint8_t v___x_923_; uint64_t v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; uint8_t v___x_932_; uint8_t v___x_933_; uint8_t v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___y_947_; uint8_t v___x_948_; lean_object* v___x_949_; 
lean_dec(v_attrName_891_);
v___x_912_ = 1;
v___x_913_ = 1;
v___x_914_ = 0;
v___x_915_ = 2;
v___x_916_ = lean_alloc_ctor(0, 0, 21);
v___x_917_ = lean_unbox(v_a_907_);
lean_ctor_set_uint8(v___x_916_, 0, v___x_917_);
v___x_918_ = lean_unbox(v_a_907_);
lean_ctor_set_uint8(v___x_916_, 1, v___x_918_);
v___x_919_ = lean_unbox(v_a_907_);
lean_ctor_set_uint8(v___x_916_, 2, v___x_919_);
v___x_920_ = lean_unbox(v_a_907_);
lean_ctor_set_uint8(v___x_916_, 3, v___x_920_);
v___x_921_ = lean_unbox(v_a_907_);
lean_ctor_set_uint8(v___x_916_, 4, v___x_921_);
lean_ctor_set_uint8(v___x_916_, 5, v___x_912_);
lean_ctor_set_uint8(v___x_916_, 6, v___x_912_);
v___x_922_ = lean_unbox(v_a_907_);
lean_ctor_set_uint8(v___x_916_, 7, v___x_922_);
lean_ctor_set_uint8(v___x_916_, 8, v___x_912_);
lean_ctor_set_uint8(v___x_916_, 9, v___x_913_);
lean_ctor_set_uint8(v___x_916_, 10, v___x_914_);
lean_ctor_set_uint8(v___x_916_, 11, v___x_912_);
lean_ctor_set_uint8(v___x_916_, 12, v___x_912_);
lean_ctor_set_uint8(v___x_916_, 13, v___x_912_);
lean_ctor_set_uint8(v___x_916_, 14, v___x_915_);
lean_ctor_set_uint8(v___x_916_, 15, v___x_912_);
lean_ctor_set_uint8(v___x_916_, 16, v___x_912_);
lean_ctor_set_uint8(v___x_916_, 17, v___x_912_);
lean_ctor_set_uint8(v___x_916_, 18, v___x_912_);
v___x_923_ = lean_unbox(v_a_907_);
lean_ctor_set_uint8(v___x_916_, 19, v___x_923_);
lean_ctor_set_uint8(v___x_916_, 20, v___x_912_);
v___x_924_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_916_);
v___x_925_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_925_, 0, v___x_916_);
lean_ctor_set_uint64(v___x_925_, sizeof(void*)*1, v___x_924_);
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__3);
v___x_928_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__4, &l_Lean_Meta_mkSimpAttr___lam__0___closed__4_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__4);
v___x_929_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__0___closed__5));
v___x_930_ = lean_box(0);
lean_inc(v___x_892_);
v___x_931_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_931_, 0, v___x_925_);
lean_ctor_set(v___x_931_, 1, v___x_892_);
lean_ctor_set(v___x_931_, 2, v___x_928_);
lean_ctor_set(v___x_931_, 3, v___x_929_);
lean_ctor_set(v___x_931_, 4, v___x_930_);
lean_ctor_set(v___x_931_, 5, v___x_926_);
lean_ctor_set(v___x_931_, 6, v___x_930_);
v___x_932_ = lean_unbox(v_a_907_);
lean_ctor_set_uint8(v___x_931_, sizeof(void*)*7, v___x_932_);
v___x_933_ = lean_unbox(v_a_907_);
lean_ctor_set_uint8(v___x_931_, sizeof(void*)*7 + 1, v___x_933_);
v___x_934_ = lean_unbox(v_a_907_);
lean_ctor_set_uint8(v___x_931_, sizeof(void*)*7 + 2, v___x_934_);
lean_ctor_set_uint8(v___x_931_, sizeof(void*)*7 + 3, v___x_912_);
v___x_935_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__6, &l_Lean_Meta_mkSimpAttr___lam__0___closed__6_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__6);
v___x_936_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__9, &l_Lean_Meta_mkSimpAttr___lam__0___closed__9_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__9);
v___x_937_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__0___closed__10, &l_Lean_Meta_mkSimpAttr___lam__0___closed__10_once, _init_l_Lean_Meta_mkSimpAttr___lam__0___closed__10);
v___x_938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_938_, 0, v___x_935_);
lean_ctor_set(v___x_938_, 1, v___x_936_);
lean_ctor_set(v___x_938_, 2, v___x_892_);
lean_ctor_set(v___x_938_, 3, v___x_927_);
lean_ctor_set(v___x_938_, 4, v___x_937_);
v___x_939_ = lean_box(0);
v___x_940_ = lean_st_mk_ref(v___x_938_);
v___x_948_ = lean_unbox(v_a_907_);
lean_inc(v_declName_894_);
v___x_949_ = l_Lean_getAsyncConstInfo___at___00Lean_Meta_mkSimpAttr_spec__1(v_declName_894_, v___x_948_, v___x_931_, v___x_940_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; uint8_t v___y_952_; uint8_t v___y_953_; uint8_t v___y_1002_; lean_object* v___x_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_949_, 1);
v___x_1007_ = lean_unsigned_to_nat(1u);
v___x_1008_ = l_Lean_Syntax_getArg(v_stx_895_, v___x_1007_);
v___x_1009_ = l_Lean_Syntax_isNone(v___x_1008_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1010_ = l_Lean_Syntax_getArg(v___x_1008_, v___x_926_);
lean_dec(v___x_1008_);
v___x_1011_ = l_Lean_Syntax_getKind(v___x_1010_);
v___x_1012_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___lam__1___closed__8));
v___x_1013_ = lean_name_eq(v___x_1011_, v___x_1012_);
lean_dec(v___x_1011_);
v___y_1002_ = v___x_1013_;
goto v___jp_1001_;
}
else
{
lean_dec(v___x_1008_);
v___y_1002_ = v___x_912_;
goto v___jp_1001_;
}
v___jp_951_:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_954_ = lean_unsigned_to_nat(3u);
v___x_955_ = l_Lean_Syntax_getArg(v_stx_895_, v___x_954_);
lean_dec(v_stx_895_);
v___x_956_ = l_Lean_getAttrParamOptPrio(v___x_955_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v_sig_958_; lean_object* v___x_959_; lean_object* v_type_960_; lean_object* v___x_961_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref_known(v___x_956_, 1);
v_sig_958_ = lean_ctor_get(v_a_950_, 1);
lean_inc_ref(v_sig_958_);
lean_dec(v_a_950_);
v___x_959_ = lean_task_get_own(v_sig_958_);
v_type_960_ = lean_ctor_get(v___x_959_, 2);
lean_inc_ref(v_type_960_);
lean_dec(v___x_959_);
v___x_961_ = l_Lean_Meta_isProp(v_type_960_, v___x_931_, v___x_940_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; uint8_t v___x_963_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref_known(v___x_961_, 1);
v___x_963_ = lean_unbox(v_a_962_);
lean_dec(v_a_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; 
lean_inc(v_declName_894_);
v___x_964_ = l_Lean_Meta_addDeclToUnfold(v_ext_893_, v_declName_894_, v___y_952_, v___y_953_, v_a_957_, v_attrKind_896_, v___x_931_, v___x_940_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; uint8_t v___x_966_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v___x_964_, 1);
v___x_966_ = lean_unbox(v_a_965_);
lean_dec(v_a_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; uint8_t v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_967_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__1___closed__1, &l_Lean_Meta_mkSimpAttr___lam__1___closed__1_once, _init_l_Lean_Meta_mkSimpAttr___lam__1___closed__1);
v___x_968_ = lean_unbox(v_a_907_);
lean_dec(v_a_907_);
v___x_969_ = l_Lean_MessageData_ofConstName(v_declName_894_, v___x_968_);
v___x_970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_967_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__1___closed__3, &l_Lean_Meta_mkSimpAttr___lam__1___closed__3_once, _init_l_Lean_Meta_mkSimpAttr___lam__1___closed__3);
v___x_972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___lam__1___closed__6, &l_Lean_Meta_mkSimpAttr___lam__1___closed__6_once, _init_l_Lean_Meta_mkSimpAttr___lam__1___closed__6);
v___x_974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = l_Lean_throwError___at___00Lean_Meta_addDeclToUnfold_spec__3___redArg(v___x_974_, v___x_931_, v___x_940_, v___y_897_, v___y_898_);
lean_dec_ref_known(v___x_931_, 7);
v___y_947_ = v___x_975_;
goto v___jp_946_;
}
else
{
lean_dec_ref_known(v___x_931_, 7);
lean_dec(v_a_907_);
lean_dec(v_declName_894_);
goto v___jp_941_;
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec(v___x_940_);
lean_dec_ref_known(v___x_931_, 7);
lean_del_object(v___x_909_);
lean_dec(v_a_907_);
lean_dec(v_declName_894_);
v_a_976_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_964_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_964_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
else
{
lean_object* v___x_984_; 
lean_dec(v_a_907_);
v___x_984_ = l_Lean_Meta_addSimpTheorem(v_ext_893_, v_declName_894_, v___y_952_, v___y_953_, v_attrKind_896_, v_a_957_, v___x_931_, v___x_940_, v___y_897_, v___y_898_);
lean_dec_ref_known(v___x_931_, 7);
v___y_947_ = v___x_984_;
goto v___jp_946_;
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec(v_a_957_);
lean_dec(v___x_940_);
lean_dec_ref_known(v___x_931_, 7);
lean_del_object(v___x_909_);
lean_dec(v_a_907_);
lean_dec(v_declName_894_);
lean_dec_ref(v_ext_893_);
v_a_985_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_961_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_961_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec(v_a_950_);
lean_dec(v___x_940_);
lean_dec_ref_known(v___x_931_, 7);
lean_del_object(v___x_909_);
lean_dec(v_a_907_);
lean_dec(v_declName_894_);
lean_dec_ref(v_ext_893_);
v_a_993_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_956_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_956_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
v___jp_1001_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1003_ = lean_unsigned_to_nat(2u);
v___x_1004_ = l_Lean_Syntax_getArg(v_stx_895_, v___x_1003_);
v___x_1005_ = l_Lean_Syntax_isNone(v___x_1004_);
lean_dec(v___x_1004_);
if (v___x_1005_ == 0)
{
v___y_952_ = v___y_1002_;
v___y_953_ = v___x_912_;
goto v___jp_951_;
}
else
{
uint8_t v___x_1006_; 
v___x_1006_ = lean_unbox(v_a_907_);
v___y_952_ = v___y_1002_;
v___y_953_ = v___x_1006_;
goto v___jp_951_;
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec(v___x_940_);
lean_dec_ref_known(v___x_931_, 7);
lean_del_object(v___x_909_);
lean_dec(v_a_907_);
lean_dec(v_stx_895_);
lean_dec(v_declName_894_);
lean_dec_ref(v_ext_893_);
v_a_1014_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_949_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_949_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
v___jp_941_:
{
lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_942_ = lean_st_ref_get(v___x_940_);
lean_dec(v___x_940_);
lean_dec(v___x_942_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v___x_939_);
v___x_944_ = v___x_909_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
v___jp_946_:
{
if (lean_obj_tag(v___y_947_) == 0)
{
lean_dec_ref_known(v___y_947_, 1);
goto v___jp_941_;
}
else
{
lean_dec(v___x_940_);
lean_del_object(v___x_909_);
return v___y_947_;
}
}
}
else
{
lean_del_object(v___x_909_);
lean_dec(v_a_907_);
lean_dec_ref(v_ext_893_);
lean_dec(v___x_892_);
goto v___jp_900_;
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec(v_stx_895_);
lean_dec(v_declName_894_);
lean_dec_ref(v_ext_893_);
lean_dec(v___x_892_);
lean_dec(v_attrName_891_);
v_a_1023_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_906_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_906_);
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
lean_dec_ref(v_ext_893_);
lean_dec(v___x_892_);
goto v___jp_900_;
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec(v_stx_895_);
lean_dec(v_declName_894_);
lean_dec_ref(v_ext_893_);
lean_dec(v___x_892_);
lean_dec(v_attrName_891_);
v_a_1031_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_903_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_903_);
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
v___jp_900_:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(v_attrName_891_);
v___x_902_ = l_Lean_Attribute_add(v_declName_894_, v___x_901_, v_stx_895_, v_attrKind_896_, v___y_897_, v___y_898_);
return v___x_902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__1___boxed(lean_object* v_attrName_1039_, lean_object* v___x_1040_, lean_object* v_ext_1041_, lean_object* v_declName_1042_, lean_object* v_stx_1043_, lean_object* v_attrKind_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
uint8_t v_attrKind_boxed_1048_; lean_object* v_res_1049_; 
v_attrKind_boxed_1048_ = lean_unbox(v_attrKind_1044_);
v_res_1049_ = l_Lean_Meta_mkSimpAttr___lam__1(v_attrName_1039_, v___x_1040_, v_ext_1041_, v_declName_1042_, v_stx_1043_, v_attrKind_boxed_1048_, v___y_1045_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__2(lean_object* v_a_1050_, lean_object* v_x_1051_){
_start:
{
lean_inc_ref(v_a_1050_);
return v_a_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__2___boxed(lean_object* v_a_1052_, lean_object* v_x_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_Meta_mkSimpAttr___lam__2(v_a_1052_, v_x_1053_);
lean_dec_ref(v_x_1053_);
lean_dec_ref(v_a_1052_);
return v_res_1054_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7_spec__10___redArg(lean_object* v_keys_1055_, lean_object* v_i_1056_, lean_object* v_k_1057_){
_start:
{
lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1058_ = lean_array_get_size(v_keys_1055_);
v___x_1059_ = lean_nat_dec_lt(v_i_1056_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_dec(v_i_1056_);
return v___x_1059_;
}
else
{
lean_object* v_k_x27_1060_; uint8_t v___x_1061_; 
v_k_x27_1060_ = lean_array_fget_borrowed(v_keys_1055_, v_i_1056_);
v___x_1061_ = lean_name_eq(v_k_1057_, v_k_x27_1060_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_unsigned_to_nat(1u);
v___x_1063_ = lean_nat_add(v_i_1056_, v___x_1062_);
lean_dec(v_i_1056_);
v_i_1056_ = v___x_1063_;
goto _start;
}
else
{
lean_dec(v_i_1056_);
return v___x_1059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_keys_1065_, lean_object* v_i_1066_, lean_object* v_k_1067_){
_start:
{
uint8_t v_res_1068_; lean_object* v_r_1069_; 
v_res_1068_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7_spec__10___redArg(v_keys_1065_, v_i_1066_, v_k_1067_);
lean_dec(v_k_1067_);
lean_dec_ref(v_keys_1065_);
v_r_1069_ = lean_box(v_res_1068_);
return v_r_1069_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7___redArg(lean_object* v_x_1070_, size_t v_x_1071_, lean_object* v_x_1072_){
_start:
{
if (lean_obj_tag(v_x_1070_) == 0)
{
lean_object* v_es_1073_; lean_object* v___x_1074_; size_t v___x_1075_; size_t v___x_1076_; lean_object* v_j_1077_; lean_object* v___x_1078_; 
v_es_1073_ = lean_ctor_get(v_x_1070_, 0);
v___x_1074_ = lean_box(2);
v___x_1075_ = ((size_t)31ULL);
v___x_1076_ = lean_usize_land(v_x_1071_, v___x_1075_);
v_j_1077_ = lean_usize_to_nat(v___x_1076_);
v___x_1078_ = lean_array_get_borrowed(v___x_1074_, v_es_1073_, v_j_1077_);
lean_dec(v_j_1077_);
switch(lean_obj_tag(v___x_1078_))
{
case 0:
{
lean_object* v_key_1079_; uint8_t v___x_1080_; 
v_key_1079_ = lean_ctor_get(v___x_1078_, 0);
v___x_1080_ = lean_name_eq(v_x_1072_, v_key_1079_);
return v___x_1080_;
}
case 1:
{
lean_object* v_node_1081_; size_t v___x_1082_; size_t v___x_1083_; 
v_node_1081_ = lean_ctor_get(v___x_1078_, 0);
v___x_1082_ = ((size_t)5ULL);
v___x_1083_ = lean_usize_shift_right(v_x_1071_, v___x_1082_);
v_x_1070_ = v_node_1081_;
v_x_1071_ = v___x_1083_;
goto _start;
}
default: 
{
uint8_t v___x_1085_; 
v___x_1085_ = 0;
return v___x_1085_;
}
}
}
else
{
lean_object* v_ks_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v_ks_1086_ = lean_ctor_get(v_x_1070_, 0);
v___x_1087_ = lean_unsigned_to_nat(0u);
v___x_1088_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7_spec__10___redArg(v_ks_1086_, v___x_1087_, v_x_1072_);
return v___x_1088_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_x_1089_, lean_object* v_x_1090_, lean_object* v_x_1091_){
_start:
{
size_t v_x_11204__boxed_1092_; uint8_t v_res_1093_; lean_object* v_r_1094_; 
v_x_11204__boxed_1092_ = lean_unbox_usize(v_x_1090_);
lean_dec(v_x_1090_);
v_res_1093_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7___redArg(v_x_1089_, v_x_11204__boxed_1092_, v_x_1091_);
lean_dec(v_x_1091_);
lean_dec_ref(v_x_1089_);
v_r_1094_ = lean_box(v_res_1093_);
return v_r_1094_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4___redArg(lean_object* v_x_1095_, lean_object* v_x_1096_){
_start:
{
uint64_t v___y_1098_; 
if (lean_obj_tag(v_x_1096_) == 0)
{
uint64_t v___x_1101_; 
v___x_1101_ = 1723ULL;
v___y_1098_ = v___x_1101_;
goto v___jp_1097_;
}
else
{
uint64_t v_hash_1102_; 
v_hash_1102_ = lean_ctor_get_uint64(v_x_1096_, sizeof(void*)*2);
v___y_1098_ = v_hash_1102_;
goto v___jp_1097_;
}
v___jp_1097_:
{
size_t v___x_1099_; uint8_t v___x_1100_; 
v___x_1099_ = lean_uint64_to_usize(v___y_1098_);
v___x_1100_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7___redArg(v_x_1095_, v___x_1099_, v_x_1096_);
return v___x_1100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4___redArg___boxed(lean_object* v_x_1103_, lean_object* v_x_1104_){
_start:
{
uint8_t v_res_1105_; lean_object* v_r_1106_; 
v_res_1105_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4___redArg(v_x_1103_, v_x_1104_);
lean_dec(v_x_1104_);
lean_dec_ref(v_x_1103_);
v_r_1106_ = lean_box(v_res_1105_);
return v_r_1106_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7_spec__12(lean_object* v_opts_1107_, lean_object* v_opt_1108_){
_start:
{
lean_object* v_name_1109_; lean_object* v_defValue_1110_; lean_object* v_map_1111_; lean_object* v___x_1112_; 
v_name_1109_ = lean_ctor_get(v_opt_1108_, 0);
v_defValue_1110_ = lean_ctor_get(v_opt_1108_, 1);
v_map_1111_ = lean_ctor_get(v_opts_1107_, 0);
v___x_1112_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1111_, v_name_1109_);
if (lean_obj_tag(v___x_1112_) == 0)
{
uint8_t v___x_1113_; 
v___x_1113_ = lean_unbox(v_defValue_1110_);
return v___x_1113_;
}
else
{
lean_object* v_val_1114_; 
v_val_1114_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_val_1114_);
lean_dec_ref_known(v___x_1112_, 1);
if (lean_obj_tag(v_val_1114_) == 1)
{
uint8_t v_v_1115_; 
v_v_1115_ = lean_ctor_get_uint8(v_val_1114_, 0);
lean_dec_ref_known(v_val_1114_, 0);
return v_v_1115_;
}
else
{
uint8_t v___x_1116_; 
lean_dec(v_val_1114_);
v___x_1116_ = lean_unbox(v_defValue_1110_);
return v___x_1116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7_spec__12___boxed(lean_object* v_opts_1117_, lean_object* v_opt_1118_){
_start:
{
uint8_t v_res_1119_; lean_object* v_r_1120_; 
v_res_1119_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7_spec__12(v_opts_1117_, v_opt_1118_);
lean_dec_ref(v_opt_1118_);
lean_dec_ref(v_opts_1117_);
v_r_1120_ = lean_box(v_res_1119_);
return v_r_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7_spec__11(lean_object* v_msgData_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1125_; lean_object* v_toCold_1126_; lean_object* v_env_1127_; lean_object* v_options_1128_; uint8_t v___x_1129_; lean_object* v_env_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1125_ = lean_st_ref_get(v___y_1123_);
v_toCold_1126_ = lean_ctor_get(v___y_1122_, 0);
v_env_1127_ = lean_ctor_get(v___x_1125_, 0);
lean_inc_ref(v_env_1127_);
lean_dec(v___x_1125_);
v_options_1128_ = lean_ctor_get(v_toCold_1126_, 2);
v___x_1129_ = 0;
v_env_1130_ = l_Lean_Environment_setRecordingDeps(v_env_1127_, v___x_1129_);
v___x_1131_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__1);
v___x_1132_ = lean_unsigned_to_nat(32u);
v___x_1133_ = lean_mk_empty_array_with_capacity(v___x_1132_);
lean_dec_ref(v___x_1133_);
v___x_1134_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg___closed__4);
lean_inc_ref(v_options_1128_);
v___x_1135_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1135_, 0, v_env_1130_);
lean_ctor_set(v___x_1135_, 1, v___x_1131_);
lean_ctor_set(v___x_1135_, 2, v___x_1134_);
lean_ctor_set(v___x_1135_, 3, v_options_1128_);
v___x_1136_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v_msgData_1121_);
v___x_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7_spec__11___boxed(lean_object* v_msgData_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7_spec__11(v_msgData_1138_, v___y_1139_, v___y_1140_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
return v_res_1142_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0(uint8_t v_suppressElabErrors_1150_, lean_object* v_x_1151_){
_start:
{
if (lean_obj_tag(v_x_1151_) == 1)
{
lean_object* v_pre_1152_; 
v_pre_1152_ = lean_ctor_get(v_x_1151_, 0);
switch(lean_obj_tag(v_pre_1152_))
{
case 1:
{
lean_object* v_pre_1153_; 
v_pre_1153_ = lean_ctor_get(v_pre_1152_, 0);
switch(lean_obj_tag(v_pre_1153_))
{
case 0:
{
lean_object* v_str_1154_; lean_object* v_str_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; 
v_str_1154_ = lean_ctor_get(v_x_1151_, 1);
v_str_1155_ = lean_ctor_get(v_pre_1152_, 1);
v___x_1156_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__0));
v___x_1157_ = lean_string_dec_eq(v_str_1155_, v___x_1156_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1158_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___auto__1___closed__2));
v___x_1159_ = lean_string_dec_eq(v_str_1155_, v___x_1158_);
if (v___x_1159_ == 0)
{
return v___x_1159_;
}
else
{
lean_object* v___x_1160_; uint8_t v___x_1161_; 
v___x_1160_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__1));
v___x_1161_ = lean_string_dec_eq(v_str_1154_, v___x_1160_);
if (v___x_1161_ == 0)
{
return v___x_1161_;
}
else
{
return v_suppressElabErrors_1150_;
}
}
}
else
{
lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__2));
v___x_1163_ = lean_string_dec_eq(v_str_1154_, v___x_1162_);
if (v___x_1163_ == 0)
{
return v___x_1163_;
}
else
{
return v_suppressElabErrors_1150_;
}
}
}
case 1:
{
lean_object* v_pre_1164_; 
v_pre_1164_ = lean_ctor_get(v_pre_1153_, 0);
if (lean_obj_tag(v_pre_1164_) == 0)
{
lean_object* v_str_1165_; lean_object* v_str_1166_; lean_object* v_str_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v_str_1165_ = lean_ctor_get(v_x_1151_, 1);
v_str_1166_ = lean_ctor_get(v_pre_1152_, 1);
v_str_1167_ = lean_ctor_get(v_pre_1153_, 1);
v___x_1168_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__3));
v___x_1169_ = lean_string_dec_eq(v_str_1167_, v___x_1168_);
if (v___x_1169_ == 0)
{
return v___x_1169_;
}
else
{
lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__4));
v___x_1171_ = lean_string_dec_eq(v_str_1166_, v___x_1170_);
if (v___x_1171_ == 0)
{
return v___x_1171_;
}
else
{
lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__5));
v___x_1173_ = lean_string_dec_eq(v_str_1165_, v___x_1172_);
if (v___x_1173_ == 0)
{
return v___x_1173_;
}
else
{
return v_suppressElabErrors_1150_;
}
}
}
}
else
{
uint8_t v___x_1174_; 
v___x_1174_ = 0;
return v___x_1174_;
}
}
default: 
{
uint8_t v___x_1175_; 
v___x_1175_ = 0;
return v___x_1175_;
}
}
}
case 0:
{
lean_object* v_str_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v_str_1176_ = lean_ctor_get(v_x_1151_, 1);
v___x_1177_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___closed__6));
v___x_1178_ = lean_string_dec_eq(v_str_1176_, v___x_1177_);
if (v___x_1178_ == 0)
{
return v___x_1178_;
}
else
{
return v_suppressElabErrors_1150_;
}
}
default: 
{
uint8_t v___x_1179_; 
v___x_1179_ = 0;
return v___x_1179_;
}
}
}
else
{
uint8_t v___x_1180_; 
v___x_1180_ = 0;
return v___x_1180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___boxed(lean_object* v_suppressElabErrors_1181_, lean_object* v_x_1182_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1183_; uint8_t v_res_1184_; lean_object* v_r_1185_; 
v_suppressElabErrors_boxed_1183_ = lean_unbox(v_suppressElabErrors_1181_);
v_res_1184_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0(v_suppressElabErrors_boxed_1183_, v_x_1182_);
lean_dec(v_x_1182_);
v_r_1185_ = lean_box(v_res_1184_);
return v_r_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7(lean_object* v_ref_1187_, lean_object* v_msgData_1188_, uint8_t v_severity_1189_, uint8_t v_isSilent_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___y_1195_; uint8_t v___y_1196_; uint8_t v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v_toCold_1202_; lean_object* v___y_1203_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; uint8_t v___y_1235_; uint8_t v___y_1236_; uint8_t v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1259_; lean_object* v___y_1260_; uint8_t v___y_1261_; uint8_t v___y_1262_; uint8_t v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; uint8_t v___y_1269_; uint8_t v___y_1270_; uint8_t v___x_1280_; uint8_t v___y_1282_; uint8_t v___x_1288_; 
v___x_1280_ = 2;
v___x_1288_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1189_, v___x_1280_);
if (v___x_1288_ == 0)
{
v___y_1282_ = v___x_1288_;
goto v___jp_1281_;
}
else
{
uint8_t v___x_1289_; 
lean_inc_ref(v_msgData_1188_);
v___x_1289_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1188_);
if (v___x_1289_ == 0)
{
v___y_1282_ = v___x_1289_;
goto v___jp_1281_;
}
else
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
lean_dec_ref(v_msgData_1188_);
v___x_1290_ = lean_box(0);
v___x_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
return v___x_1291_;
}
}
v___jp_1194_:
{
lean_object* v_currNamespace_1204_; lean_object* v_openDecls_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v_env_1210_; lean_object* v_nextMacroScope_1211_; lean_object* v_ngen_1212_; lean_object* v_auxDeclNGen_1213_; lean_object* v_traceState_1214_; lean_object* v_cache_1215_; lean_object* v_recordedDeps_1216_; lean_object* v_messages_1217_; lean_object* v_infoState_1218_; lean_object* v_snapshotTasks_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1230_; 
v_currNamespace_1204_ = lean_ctor_get(v_toCold_1202_, 4);
v_openDecls_1205_ = lean_ctor_get(v_toCold_1202_, 5);
lean_inc(v_openDecls_1205_);
lean_inc(v_currNamespace_1204_);
v___x_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1206_, 0, v_currNamespace_1204_);
lean_ctor_set(v___x_1206_, 1, v_openDecls_1205_);
v___x_1207_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
lean_ctor_set(v___x_1207_, 1, v___y_1201_);
lean_inc_ref(v___y_1195_);
lean_inc_ref(v___y_1200_);
v___x_1208_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1208_, 0, v___y_1200_);
lean_ctor_set(v___x_1208_, 1, v___y_1198_);
lean_ctor_set(v___x_1208_, 2, v___y_1199_);
lean_ctor_set(v___x_1208_, 3, v___y_1195_);
lean_ctor_set(v___x_1208_, 4, v___x_1207_);
lean_ctor_set_uint8(v___x_1208_, sizeof(void*)*5, v___y_1197_);
lean_ctor_set_uint8(v___x_1208_, sizeof(void*)*5 + 1, v___y_1196_);
lean_ctor_set_uint8(v___x_1208_, sizeof(void*)*5 + 2, v_isSilent_1190_);
v___x_1209_ = lean_st_ref_take(v___y_1203_);
v_env_1210_ = lean_ctor_get(v___x_1209_, 0);
v_nextMacroScope_1211_ = lean_ctor_get(v___x_1209_, 1);
v_ngen_1212_ = lean_ctor_get(v___x_1209_, 2);
v_auxDeclNGen_1213_ = lean_ctor_get(v___x_1209_, 3);
v_traceState_1214_ = lean_ctor_get(v___x_1209_, 4);
v_cache_1215_ = lean_ctor_get(v___x_1209_, 5);
v_recordedDeps_1216_ = lean_ctor_get(v___x_1209_, 6);
v_messages_1217_ = lean_ctor_get(v___x_1209_, 7);
v_infoState_1218_ = lean_ctor_get(v___x_1209_, 8);
v_snapshotTasks_1219_ = lean_ctor_get(v___x_1209_, 9);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1221_ = v___x_1209_;
v_isShared_1222_ = v_isSharedCheck_1230_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_snapshotTasks_1219_);
lean_inc(v_infoState_1218_);
lean_inc(v_messages_1217_);
lean_inc(v_recordedDeps_1216_);
lean_inc(v_cache_1215_);
lean_inc(v_traceState_1214_);
lean_inc(v_auxDeclNGen_1213_);
lean_inc(v_ngen_1212_);
lean_inc(v_nextMacroScope_1211_);
lean_inc(v_env_1210_);
lean_dec(v___x_1209_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1230_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1223_ = lean_box(0);
v___x_1224_ = l_Lean_MessageLog_add(v___x_1208_, v_messages_1217_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 7, v___x_1224_);
v___x_1226_ = v___x_1221_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_env_1210_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_nextMacroScope_1211_);
lean_ctor_set(v_reuseFailAlloc_1229_, 2, v_ngen_1212_);
lean_ctor_set(v_reuseFailAlloc_1229_, 3, v_auxDeclNGen_1213_);
lean_ctor_set(v_reuseFailAlloc_1229_, 4, v_traceState_1214_);
lean_ctor_set(v_reuseFailAlloc_1229_, 5, v_cache_1215_);
lean_ctor_set(v_reuseFailAlloc_1229_, 6, v_recordedDeps_1216_);
lean_ctor_set(v_reuseFailAlloc_1229_, 7, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1229_, 8, v_infoState_1218_);
lean_ctor_set(v_reuseFailAlloc_1229_, 9, v_snapshotTasks_1219_);
v___x_1226_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_st_ref_put(v___y_1203_, v___x_1226_);
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1223_);
return v___x_1228_;
}
}
}
v___jp_1231_:
{
lean_object* v_fileName_1240_; lean_object* v_fileMap_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1257_; 
v_fileName_1240_ = lean_ctor_get(v___y_1234_, 0);
v_fileMap_1241_ = lean_ctor_get(v___y_1234_, 1);
v___x_1242_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1188_);
v___x_1243_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7_spec__11(v___x_1242_, v___y_1191_, v___y_1192_);
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1246_ = v___x_1243_;
v_isShared_1247_ = v_isSharedCheck_1257_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1257_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_inc_ref_n(v_fileMap_1241_, 2);
v___x_1248_ = l_Lean_FileMap_toPosition(v_fileMap_1241_, v___y_1238_);
lean_dec(v___y_1238_);
v___x_1249_ = l_Lean_FileMap_toPosition(v_fileMap_1241_, v___y_1239_);
lean_dec(v___y_1239_);
v___x_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
v___x_1251_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___closed__0));
if (v___y_1237_ == 0)
{
lean_del_object(v___x_1246_);
lean_dec_ref(v___y_1233_);
v___y_1195_ = v___x_1251_;
v___y_1196_ = v___y_1236_;
v___y_1197_ = v___y_1235_;
v___y_1198_ = v___x_1248_;
v___y_1199_ = v___x_1250_;
v___y_1200_ = v_fileName_1240_;
v___y_1201_ = v_a_1244_;
v_toCold_1202_ = v___y_1232_;
v___y_1203_ = v___y_1192_;
goto v___jp_1194_;
}
else
{
uint8_t v___x_1252_; 
lean_inc(v_a_1244_);
v___x_1252_ = l_Lean_MessageData_hasTag(v___y_1233_, v_a_1244_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1255_; 
lean_dec_ref_known(v___x_1250_, 1);
lean_dec_ref(v___x_1248_);
lean_dec(v_a_1244_);
v___x_1253_ = lean_box(0);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1253_);
v___x_1255_ = v___x_1246_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
else
{
lean_del_object(v___x_1246_);
v___y_1195_ = v___x_1251_;
v___y_1196_ = v___y_1236_;
v___y_1197_ = v___y_1235_;
v___y_1198_ = v___x_1248_;
v___y_1199_ = v___x_1250_;
v___y_1200_ = v_fileName_1240_;
v___y_1201_ = v_a_1244_;
v_toCold_1202_ = v___y_1232_;
v___y_1203_ = v___y_1192_;
goto v___jp_1194_;
}
}
}
}
v___jp_1258_:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_Syntax_getTailPos_x3f(v___y_1264_, v___y_1263_);
lean_dec(v___y_1264_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_inc(v___y_1265_);
v___y_1232_ = v___y_1259_;
v___y_1233_ = v___y_1260_;
v___y_1234_ = v___y_1259_;
v___y_1235_ = v___y_1263_;
v___y_1236_ = v___y_1262_;
v___y_1237_ = v___y_1261_;
v___y_1238_ = v___y_1265_;
v___y_1239_ = v___y_1265_;
goto v___jp_1231_;
}
else
{
lean_object* v_val_1267_; 
v_val_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_val_1267_);
lean_dec_ref_known(v___x_1266_, 1);
v___y_1232_ = v___y_1259_;
v___y_1233_ = v___y_1260_;
v___y_1234_ = v___y_1259_;
v___y_1235_ = v___y_1263_;
v___y_1236_ = v___y_1262_;
v___y_1237_ = v___y_1261_;
v___y_1238_ = v___y_1265_;
v___y_1239_ = v_val_1267_;
goto v___jp_1231_;
}
}
v___jp_1268_:
{
lean_object* v_toCold_1271_; lean_object* v_ref_1272_; uint8_t v_suppressElabErrors_1273_; lean_object* v___x_1274_; lean_object* v___f_1275_; lean_object* v_ref_1276_; lean_object* v___x_1277_; 
v_toCold_1271_ = lean_ctor_get(v___y_1191_, 0);
v_ref_1272_ = lean_ctor_get(v___y_1191_, 2);
v_suppressElabErrors_1273_ = lean_ctor_get_uint8(v___y_1191_, sizeof(void*)*3 + 2);
v___x_1274_ = lean_box(v_suppressElabErrors_1273_);
v___f_1275_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1275_, 0, v___x_1274_);
v_ref_1276_ = l_Lean_replaceRef(v_ref_1187_, v_ref_1272_);
v___x_1277_ = l_Lean_Syntax_getPos_x3f(v_ref_1276_, v___y_1269_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v___x_1278_; 
v___x_1278_ = lean_unsigned_to_nat(0u);
v___y_1259_ = v_toCold_1271_;
v___y_1260_ = v___f_1275_;
v___y_1261_ = v_suppressElabErrors_1273_;
v___y_1262_ = v___y_1270_;
v___y_1263_ = v___y_1269_;
v___y_1264_ = v_ref_1276_;
v___y_1265_ = v___x_1278_;
goto v___jp_1258_;
}
else
{
lean_object* v_val_1279_; 
v_val_1279_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_val_1279_);
lean_dec_ref_known(v___x_1277_, 1);
v___y_1259_ = v_toCold_1271_;
v___y_1260_ = v___f_1275_;
v___y_1261_ = v_suppressElabErrors_1273_;
v___y_1262_ = v___y_1270_;
v___y_1263_ = v___y_1269_;
v___y_1264_ = v_ref_1276_;
v___y_1265_ = v_val_1279_;
goto v___jp_1258_;
}
}
v___jp_1281_:
{
uint8_t v___x_1283_; uint8_t v___x_1284_; 
v___x_1283_ = 1;
v___x_1284_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1189_, v___x_1283_);
if (v___x_1284_ == 0)
{
v___y_1269_ = v___y_1282_;
v___y_1270_ = v_severity_1189_;
goto v___jp_1268_;
}
else
{
lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1285_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1191_);
v___x_1286_ = l_Lean_warningAsError;
v___x_1287_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7_spec__12(v___x_1285_, v___x_1286_);
lean_dec_ref(v___x_1285_);
if (v___x_1287_ == 0)
{
v___y_1269_ = v___y_1282_;
v___y_1270_ = v_severity_1189_;
goto v___jp_1268_;
}
else
{
v___y_1269_ = v___y_1282_;
v___y_1270_ = v___x_1280_;
goto v___jp_1268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_ref_1292_, lean_object* v_msgData_1293_, lean_object* v_severity_1294_, lean_object* v_isSilent_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
uint8_t v_severity_boxed_1299_; uint8_t v_isSilent_boxed_1300_; lean_object* v_res_1301_; 
v_severity_boxed_1299_ = lean_unbox(v_severity_1294_);
v_isSilent_boxed_1300_ = lean_unbox(v_isSilent_1295_);
v_res_1301_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7(v_ref_1292_, v_msgData_1293_, v_severity_boxed_1299_, v_isSilent_boxed_1300_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v_ref_1292_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5(lean_object* v_msgData_1302_, uint8_t v_severity_1303_, uint8_t v_isSilent_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v_ref_1308_; lean_object* v___x_1309_; 
v_ref_1308_ = lean_ctor_get(v___y_1305_, 2);
v___x_1309_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5_spec__7(v_ref_1308_, v_msgData_1302_, v_severity_1303_, v_isSilent_1304_, v___y_1305_, v___y_1306_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5___boxed(lean_object* v_msgData_1310_, lean_object* v_severity_1311_, lean_object* v_isSilent_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
uint8_t v_severity_boxed_1316_; uint8_t v_isSilent_boxed_1317_; lean_object* v_res_1318_; 
v_severity_boxed_1316_ = lean_unbox(v_severity_1311_);
v_isSilent_boxed_1317_ = lean_unbox(v_isSilent_1312_);
v_res_1318_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5(v_msgData_1310_, v_severity_boxed_1316_, v_isSilent_boxed_1317_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3(lean_object* v_msgData_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
uint8_t v___x_1323_; uint8_t v___x_1324_; lean_object* v___x_1325_; 
v___x_1323_ = 1;
v___x_1324_ = 0;
v___x_1325_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3_spec__5(v_msgData_1319_, v___x_1323_, v___x_1324_, v___y_1320_, v___y_1321_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3___boxed(lean_object* v_msgData_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3(v_msgData_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
return v_res_1330_;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = ((lean_object*)(l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2___closed__0));
v___x_1333_ = l_Lean_stringToMessageData(v___x_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2(lean_object* v_d_1334_, lean_object* v_thmId_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
uint8_t v___x_1378_; 
v___x_1378_ = l_Lean_Meta_SimpTheorems_isLemma(v_d_1334_, v_thmId_1335_);
if (v___x_1378_ == 0)
{
if (lean_obj_tag(v_thmId_1335_) == 0)
{
lean_object* v_declName_1379_; uint8_t v___x_1380_; 
v_declName_1379_ = lean_ctor_get(v_thmId_1335_, 0);
v___x_1380_ = l_Lean_Meta_SimpTheorems_isDeclToUnfold(v_d_1334_, v_declName_1379_);
if (v___x_1380_ == 0)
{
lean_object* v_toUnfoldThms_1381_; uint8_t v___x_1382_; 
v_toUnfoldThms_1381_ = lean_ctor_get(v_d_1334_, 5);
v___x_1382_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4___redArg(v_toUnfoldThms_1381_, v_declName_1379_);
if (v___x_1382_ == 0)
{
goto v___jp_1366_;
}
else
{
goto v___jp_1339_;
}
}
else
{
goto v___jp_1339_;
}
}
else
{
goto v___jp_1366_;
}
}
else
{
goto v___jp_1339_;
}
v___jp_1339_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = l_Lean_Meta_SimpTheorems_eraseCore(v_d_1334_, v_thmId_1335_);
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
return v___x_1341_;
}
v___jp_1342_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1343_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1344_ = l_Lean_Meta_Origin_key(v_thmId_1335_);
lean_dec_ref(v_thmId_1335_);
v___x_1345_ = l_Lean_MessageData_ofName(v___x_1344_);
v___x_1346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1343_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v___x_1347_ = lean_obj_once(&l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2___closed__1, &l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2___closed__1_once, _init_l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2___closed__1);
v___x_1348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1346_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = l_Lean_logWarning___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__3(v___x_1348_, v___y_1336_, v___y_1337_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1356_ == 0)
{
lean_object* v_unused_1357_; 
v_unused_1357_ = lean_ctor_get(v___x_1349_, 0);
lean_dec(v_unused_1357_);
v___x_1351_ = v___x_1349_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_dec(v___x_1349_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v_d_1334_);
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_d_1334_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec_ref(v_d_1334_);
v_a_1358_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1349_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1349_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
v___jp_1366_:
{
lean_object* v___x_1367_; 
lean_inc_ref(v_thmId_1335_);
v___x_1367_ = l_Lean_Meta_Origin_converse(v_thmId_1335_);
if (lean_obj_tag(v___x_1367_) == 1)
{
lean_object* v_val_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1377_; 
v_val_1368_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1370_ = v___x_1367_;
v_isShared_1371_ = v_isSharedCheck_1377_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_val_1368_);
lean_dec(v___x_1367_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1377_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
uint8_t v___x_1372_; 
v___x_1372_ = l_Lean_Meta_SimpTheorems_isLemma(v_d_1334_, v_val_1368_);
if (v___x_1372_ == 0)
{
lean_del_object(v___x_1370_);
lean_dec(v_val_1368_);
goto v___jp_1342_;
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1375_; 
lean_dec_ref(v_thmId_1335_);
v___x_1373_ = l_Lean_Meta_SimpTheorems_eraseCore(v_d_1334_, v_val_1368_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set_tag(v___x_1370_, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1373_);
v___x_1375_ = v___x_1370_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
else
{
lean_dec(v___x_1367_);
goto v___jp_1342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2___boxed(lean_object* v_d_1383_, lean_object* v_thmId_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2(v_d_1383_, v_thmId_1384_, v___y_1385_, v___y_1386_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__3(lean_object* v_attrName_1389_, lean_object* v_ext_1390_, lean_object* v___x_1391_, lean_object* v_declName_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v___x_1399_; 
lean_inc(v_declName_1392_);
v___x_1399_ = l_Lean_Meta_Simp_isSimproc___redArg(v_declName_1392_, v___y_1394_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; uint8_t v___x_1401_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_a_1400_);
lean_dec_ref_known(v___x_1399_, 1);
v___x_1401_ = lean_unbox(v_a_1400_);
lean_dec(v_a_1400_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Lean_Meta_Simp_isBuiltinSimproc___redArg(v_declName_1392_, v___y_1394_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; uint8_t v___x_1404_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_a_1403_);
lean_dec_ref_known(v___x_1402_, 1);
v___x_1404_ = lean_unbox(v_a_1403_);
if (v___x_1404_ == 0)
{
uint8_t v___x_1405_; lean_object* v___x_1406_; lean_object* v_ext_1407_; lean_object* v_toEnvExtension_1408_; lean_object* v_env_1409_; lean_object* v_asyncMode_1410_; uint8_t v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; lean_object* v___x_1415_; 
lean_dec(v_attrName_1389_);
v___x_1405_ = 1;
v___x_1406_ = lean_st_ref_get(v___y_1394_);
v_ext_1407_ = lean_ctor_get(v_ext_1390_, 1);
v_toEnvExtension_1408_ = lean_ctor_get(v_ext_1407_, 0);
v_env_1409_ = lean_ctor_get(v___x_1406_, 0);
lean_inc_ref(v_env_1409_);
lean_dec(v___x_1406_);
v_asyncMode_1410_ = lean_ctor_get(v_toEnvExtension_1408_, 2);
v___x_1411_ = lean_unbox(v_a_1403_);
v___x_1412_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1391_, v_ext_1390_, v_env_1409_, v_asyncMode_1410_, v___x_1411_);
v___x_1413_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1413_, 0, v_declName_1392_);
lean_ctor_set_uint8(v___x_1413_, sizeof(void*)*1, v___x_1405_);
v___x_1414_ = lean_unbox(v_a_1403_);
lean_dec(v_a_1403_);
lean_ctor_set_uint8(v___x_1413_, sizeof(void*)*1 + 1, v___x_1414_);
v___x_1415_ = l_Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2(v___x_1412_, v___x_1413_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1446_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1446_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1446_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___f_1420_; lean_object* v___x_1421_; lean_object* v_env_1422_; lean_object* v_nextMacroScope_1423_; lean_object* v_ngen_1424_; lean_object* v_auxDeclNGen_1425_; lean_object* v_traceState_1426_; lean_object* v_recordedDeps_1427_; lean_object* v_messages_1428_; lean_object* v_infoState_1429_; lean_object* v_snapshotTasks_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1444_; 
v___f_1420_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1420_, 0, v_a_1416_);
v___x_1421_ = lean_st_ref_take(v___y_1394_);
v_env_1422_ = lean_ctor_get(v___x_1421_, 0);
v_nextMacroScope_1423_ = lean_ctor_get(v___x_1421_, 1);
v_ngen_1424_ = lean_ctor_get(v___x_1421_, 2);
v_auxDeclNGen_1425_ = lean_ctor_get(v___x_1421_, 3);
v_traceState_1426_ = lean_ctor_get(v___x_1421_, 4);
v_recordedDeps_1427_ = lean_ctor_get(v___x_1421_, 6);
v_messages_1428_ = lean_ctor_get(v___x_1421_, 7);
v_infoState_1429_ = lean_ctor_get(v___x_1421_, 8);
v_snapshotTasks_1430_ = lean_ctor_get(v___x_1421_, 9);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1444_ == 0)
{
lean_object* v_unused_1445_; 
v_unused_1445_ = lean_ctor_get(v___x_1421_, 5);
lean_dec(v_unused_1445_);
v___x_1432_ = v___x_1421_;
v_isShared_1433_ = v_isSharedCheck_1444_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_snapshotTasks_1430_);
lean_inc(v_infoState_1429_);
lean_inc(v_messages_1428_);
lean_inc(v_recordedDeps_1427_);
lean_inc(v_traceState_1426_);
lean_inc(v_auxDeclNGen_1425_);
lean_inc(v_ngen_1424_);
lean_inc(v_nextMacroScope_1423_);
lean_inc(v_env_1422_);
lean_dec(v___x_1421_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1444_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1434_ = lean_box(0);
v___x_1435_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1390_, v_env_1422_, v___f_1420_);
v___x_1436_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addDeclToUnfold_spec__2___redArg___closed__1);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 5, v___x_1436_);
lean_ctor_set(v___x_1432_, 0, v___x_1435_);
v___x_1438_ = v___x_1432_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1435_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_nextMacroScope_1423_);
lean_ctor_set(v_reuseFailAlloc_1443_, 2, v_ngen_1424_);
lean_ctor_set(v_reuseFailAlloc_1443_, 3, v_auxDeclNGen_1425_);
lean_ctor_set(v_reuseFailAlloc_1443_, 4, v_traceState_1426_);
lean_ctor_set(v_reuseFailAlloc_1443_, 5, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1443_, 6, v_recordedDeps_1427_);
lean_ctor_set(v_reuseFailAlloc_1443_, 7, v_messages_1428_);
lean_ctor_set(v_reuseFailAlloc_1443_, 8, v_infoState_1429_);
lean_ctor_set(v_reuseFailAlloc_1443_, 9, v_snapshotTasks_1430_);
v___x_1438_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1439_ = lean_st_ref_put(v___y_1394_, v___x_1438_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1434_);
v___x_1441_ = v___x_1418_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1434_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec_ref(v_ext_1390_);
v_a_1447_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1415_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1415_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
else
{
lean_dec(v_a_1403_);
lean_dec_ref(v_ext_1390_);
goto v___jp_1396_;
}
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_dec(v_declName_1392_);
lean_dec_ref(v_ext_1390_);
lean_dec(v_attrName_1389_);
v_a_1455_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1402_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1402_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
else
{
lean_dec_ref(v_ext_1390_);
goto v___jp_1396_;
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec(v_declName_1392_);
lean_dec_ref(v_ext_1390_);
lean_dec(v_attrName_1389_);
v_a_1463_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1399_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1399_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
v___jp_1396_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(v_attrName_1389_);
v___x_1398_ = l_Lean_Attribute_erase(v_declName_1392_, v___x_1397_, v___y_1393_, v___y_1394_);
return v___x_1398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__3___boxed(lean_object* v_attrName_1471_, lean_object* v_ext_1472_, lean_object* v___x_1473_, lean_object* v_declName_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Lean_Meta_mkSimpAttr___lam__3(v_attrName_1471_, v_ext_1472_, v___x_1473_, v_declName_1474_, v___y_1475_, v___y_1476_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec_ref(v___x_1473_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr(lean_object* v_attrName_1481_, lean_object* v_attrDescr_1482_, lean_object* v_ext_1483_, lean_object* v_ref_1484_){
_start:
{
lean_object* v___x_1486_; lean_object* v___f_1487_; lean_object* v___f_1488_; lean_object* v___x_1489_; lean_object* v___f_1490_; lean_object* v___x_1491_; 
v___x_1486_ = lean_box(1);
v___f_1487_ = ((lean_object*)(l_Lean_Meta_mkSimpAttr___closed__0));
lean_inc_ref(v_ext_1483_);
lean_inc_n(v_attrName_1481_, 3);
v___f_1488_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lam__1___boxed), 9, 3);
lean_closure_set(v___f_1488_, 0, v_attrName_1481_);
lean_closure_set(v___f_1488_, 1, v___x_1486_);
lean_closure_set(v___f_1488_, 2, v_ext_1483_);
v___x_1489_ = l_Lean_Meta_instInhabitedSimpTheorems_default;
v___f_1490_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lam__3___boxed), 7, 3);
lean_closure_set(v___f_1490_, 0, v_attrName_1481_);
lean_closure_set(v___f_1490_, 1, v_ext_1483_);
lean_closure_set(v___f_1490_, 2, v___x_1489_);
v___x_1491_ = l_Lean_registerAutomationAttr(v_attrName_1481_, v___f_1487_);
if (lean_obj_tag(v___x_1491_) == 0)
{
uint8_t v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
lean_dec_ref_known(v___x_1491_, 1);
v___x_1492_ = 1;
v___x_1493_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1493_, 0, v_ref_1484_);
lean_ctor_set(v___x_1493_, 1, v_attrName_1481_);
lean_ctor_set(v___x_1493_, 2, v_attrDescr_1482_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*3, v___x_1492_);
v___x_1494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
lean_ctor_set(v___x_1494_, 1, v___f_1488_);
lean_ctor_set(v___x_1494_, 2, v___f_1490_);
v___x_1495_ = l_Lean_registerBuiltinAttribute(v___x_1494_);
return v___x_1495_;
}
else
{
lean_dec_ref(v___f_1490_);
lean_dec_ref(v___f_1488_);
lean_dec(v_ref_1484_);
lean_dec_ref(v_attrDescr_1482_);
lean_dec(v_attrName_1481_);
return v___x_1491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___boxed(lean_object* v_attrName_1496_, lean_object* v_attrDescr_1497_, lean_object* v_ext_1498_, lean_object* v_ref_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_Meta_mkSimpAttr(v_attrName_1496_, v_attrDescr_1497_, v_ext_1498_, v_ref_1499_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0(lean_object* v_00_u03b1_1502_, lean_object* v_constName_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___redArg(v_constName_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1510_, lean_object* v_constName_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0(v_00_u03b1_1510_, v_constName_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
return v_res_1517_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4(lean_object* v_00_u03b2_1518_, lean_object* v_x_1519_, lean_object* v_x_1520_){
_start:
{
uint8_t v___x_1521_; 
v___x_1521_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4___redArg(v_x_1519_, v_x_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1522_, lean_object* v_x_1523_, lean_object* v_x_1524_){
_start:
{
uint8_t v_res_1525_; lean_object* v_r_1526_; 
v_res_1525_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4(v_00_u03b2_1522_, v_x_1523_, v_x_1524_);
lean_dec(v_x_1524_);
lean_dec_ref(v_x_1523_);
v_r_1526_ = lean_box(v_res_1525_);
return v_r_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1527_, lean_object* v_ref_1528_, lean_object* v_constName_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___redArg(v_ref_1528_, v_constName_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1536_, lean_object* v_ref_1537_, lean_object* v_constName_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1(v_00_u03b1_1536_, v_ref_1537_, v_constName_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v_ref_1537_);
return v_res_1544_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_1545_, lean_object* v_x_1546_, size_t v_x_1547_, lean_object* v_x_1548_){
_start:
{
uint8_t v___x_1549_; 
v___x_1549_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7___redArg(v_x_1546_, v_x_1547_, v_x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1550_, lean_object* v_x_1551_, lean_object* v_x_1552_, lean_object* v_x_1553_){
_start:
{
size_t v_x_11946__boxed_1554_; uint8_t v_res_1555_; lean_object* v_r_1556_; 
v_x_11946__boxed_1554_ = lean_unbox_usize(v_x_1552_);
lean_dec(v_x_1552_);
v_res_1555_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7(v_00_u03b2_1550_, v_x_1551_, v_x_11946__boxed_1554_, v_x_1553_);
lean_dec(v_x_1553_);
lean_dec_ref(v_x_1551_);
v_r_1556_ = lean_box(v_res_1555_);
return v_r_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1557_, lean_object* v_ref_1558_, lean_object* v_msg_1559_, lean_object* v_declHint_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1558_, v_msg_1559_, v_declHint_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1567_, lean_object* v_ref_1568_, lean_object* v_msg_1569_, lean_object* v_declHint_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1567_, v_ref_1568_, v_msg_1569_, v_declHint_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v_ref_1568_);
return v_res_1576_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7_spec__10(lean_object* v_00_u03b2_1577_, lean_object* v_keys_1578_, lean_object* v_vals_1579_, lean_object* v_heq_1580_, lean_object* v_i_1581_, lean_object* v_k_1582_){
_start:
{
uint8_t v___x_1583_; 
v___x_1583_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7_spec__10___redArg(v_keys_1578_, v_i_1581_, v_k_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b2_1584_, lean_object* v_keys_1585_, lean_object* v_vals_1586_, lean_object* v_heq_1587_, lean_object* v_i_1588_, lean_object* v_k_1589_){
_start:
{
uint8_t v_res_1590_; lean_object* v_r_1591_; 
v_res_1590_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_SimpTheorems_erase___at___00Lean_Meta_mkSimpAttr_spec__2_spec__4_spec__7_spec__10(v_00_u03b2_1584_, v_keys_1585_, v_vals_1586_, v_heq_1587_, v_i_1588_, v_k_1589_);
lean_dec(v_k_1589_);
lean_dec_ref(v_vals_1586_);
lean_dec_ref(v_keys_1585_);
v_r_1591_ = lean_box(v_res_1590_);
return v_r_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10(lean_object* v_msg_1592_, lean_object* v_declHint_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___redArg(v_msg_1592_, v_declHint_1593_, v___y_1597_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___boxed(lean_object* v_msg_1600_, lean_object* v_declHint_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10(v_msg_1600_, v_declHint_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__8(lean_object* v_00_u03b1_1608_, lean_object* v_ref_1609_, lean_object* v_msg_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__8___redArg(v_ref_1609_, v_msg_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b1_1617_, lean_object* v_ref_1618_, lean_object* v_msg_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSimpAttr_spec__0_spec__0_spec__1_spec__4_spec__8(v_00_u03b1_1617_, v_ref_1618_, v_msg_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v_ref_1618_);
return v_res_1625_;
}
}
static lean_object* _init_l_Lean_Meta_registerSimpAttr___auto__1(void){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = lean_obj_once(&l_Lean_Meta_mkSimpAttr___auto__1___closed__28, &l_Lean_Meta_mkSimpAttr___auto__1___closed__28_once, _init_l_Lean_Meta_mkSimpAttr___auto__1___closed__28);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2___redArg(lean_object* v_a_1627_, lean_object* v_b_1628_, lean_object* v_x_1629_){
_start:
{
if (lean_obj_tag(v_x_1629_) == 0)
{
lean_dec(v_b_1628_);
lean_dec(v_a_1627_);
return v_x_1629_;
}
else
{
lean_object* v_key_1630_; lean_object* v_value_1631_; lean_object* v_tail_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1644_; 
v_key_1630_ = lean_ctor_get(v_x_1629_, 0);
v_value_1631_ = lean_ctor_get(v_x_1629_, 1);
v_tail_1632_ = lean_ctor_get(v_x_1629_, 2);
v_isSharedCheck_1644_ = !lean_is_exclusive(v_x_1629_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1634_ = v_x_1629_;
v_isShared_1635_ = v_isSharedCheck_1644_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_tail_1632_);
lean_inc(v_value_1631_);
lean_inc(v_key_1630_);
lean_dec(v_x_1629_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1644_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
uint8_t v___x_1636_; 
v___x_1636_ = lean_name_eq(v_key_1630_, v_a_1627_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1639_; 
v___x_1637_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2___redArg(v_a_1627_, v_b_1628_, v_tail_1632_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 2, v___x_1637_);
v___x_1639_ = v___x_1634_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_key_1630_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_value_1631_);
lean_ctor_set(v_reuseFailAlloc_1640_, 2, v___x_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
else
{
lean_object* v___x_1642_; 
lean_dec(v_value_1631_);
lean_dec(v_key_1630_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 1, v_b_1628_);
lean_ctor_set(v___x_1634_, 0, v_a_1627_);
v___x_1642_ = v___x_1634_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1627_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_b_1628_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v_tail_1632_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1645_, lean_object* v_x_1646_){
_start:
{
if (lean_obj_tag(v_x_1646_) == 0)
{
return v_x_1645_;
}
else
{
lean_object* v_key_1647_; lean_object* v_value_1648_; lean_object* v_tail_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1675_; 
v_key_1647_ = lean_ctor_get(v_x_1646_, 0);
v_value_1648_ = lean_ctor_get(v_x_1646_, 1);
v_tail_1649_ = lean_ctor_get(v_x_1646_, 2);
v_isSharedCheck_1675_ = !lean_is_exclusive(v_x_1646_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1651_ = v_x_1646_;
v_isShared_1652_ = v_isSharedCheck_1675_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_tail_1649_);
lean_inc(v_value_1648_);
lean_inc(v_key_1647_);
lean_dec(v_x_1646_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1675_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1653_; uint64_t v___y_1655_; 
v___x_1653_ = lean_array_get_size(v_x_1645_);
if (lean_obj_tag(v_key_1647_) == 0)
{
uint64_t v___x_1673_; 
v___x_1673_ = 1723ULL;
v___y_1655_ = v___x_1673_;
goto v___jp_1654_;
}
else
{
uint64_t v_hash_1674_; 
v_hash_1674_ = lean_ctor_get_uint64(v_key_1647_, sizeof(void*)*2);
v___y_1655_ = v_hash_1674_;
goto v___jp_1654_;
}
v___jp_1654_:
{
uint64_t v___x_1656_; uint64_t v___x_1657_; uint64_t v_fold_1658_; uint64_t v___x_1659_; uint64_t v___x_1660_; uint64_t v___x_1661_; size_t v___x_1662_; size_t v___x_1663_; size_t v___x_1664_; size_t v___x_1665_; size_t v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1669_; 
v___x_1656_ = 32ULL;
v___x_1657_ = lean_uint64_shift_right(v___y_1655_, v___x_1656_);
v_fold_1658_ = lean_uint64_xor(v___y_1655_, v___x_1657_);
v___x_1659_ = 16ULL;
v___x_1660_ = lean_uint64_shift_right(v_fold_1658_, v___x_1659_);
v___x_1661_ = lean_uint64_xor(v_fold_1658_, v___x_1660_);
v___x_1662_ = lean_uint64_to_usize(v___x_1661_);
v___x_1663_ = lean_usize_of_nat(v___x_1653_);
v___x_1664_ = ((size_t)1ULL);
v___x_1665_ = lean_usize_sub(v___x_1663_, v___x_1664_);
v___x_1666_ = lean_usize_land(v___x_1662_, v___x_1665_);
v___x_1667_ = lean_array_uget_borrowed(v_x_1645_, v___x_1666_);
lean_inc(v___x_1667_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 2, v___x_1667_);
v___x_1669_ = v___x_1651_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_key_1647_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_value_1648_);
lean_ctor_set(v_reuseFailAlloc_1672_, 2, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1670_; 
v___x_1670_ = lean_array_uset(v_x_1645_, v___x_1666_, v___x_1669_);
v_x_1645_ = v___x_1670_;
v_x_1646_ = v_tail_1649_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1676_, lean_object* v_source_1677_, lean_object* v_target_1678_){
_start:
{
lean_object* v___x_1679_; uint8_t v___x_1680_; 
v___x_1679_ = lean_array_get_size(v_source_1677_);
v___x_1680_ = lean_nat_dec_lt(v_i_1676_, v___x_1679_);
if (v___x_1680_ == 0)
{
lean_dec_ref(v_source_1677_);
lean_dec(v_i_1676_);
return v_target_1678_;
}
else
{
lean_object* v_es_1681_; lean_object* v___x_1682_; lean_object* v_source_1683_; lean_object* v_target_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v_es_1681_ = lean_array_fget(v_source_1677_, v_i_1676_);
v___x_1682_ = lean_box(0);
v_source_1683_ = lean_array_fset(v_source_1677_, v_i_1676_, v___x_1682_);
v_target_1684_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1678_, v_es_1681_);
v___x_1685_ = lean_unsigned_to_nat(1u);
v___x_1686_ = lean_nat_add(v_i_1676_, v___x_1685_);
lean_dec(v_i_1676_);
v_i_1676_ = v___x_1686_;
v_source_1677_ = v_source_1683_;
v_target_1678_ = v_target_1684_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1___redArg(lean_object* v_data_1688_){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v_nbuckets_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1689_ = lean_array_get_size(v_data_1688_);
v___x_1690_ = lean_unsigned_to_nat(2u);
v_nbuckets_1691_ = lean_nat_mul(v___x_1689_, v___x_1690_);
v___x_1692_ = lean_unsigned_to_nat(0u);
v___x_1693_ = lean_box(0);
v___x_1694_ = lean_mk_array(v_nbuckets_1691_, v___x_1693_);
v___x_1695_ = lean_array_propagate_mark(v_data_1688_, v___x_1694_);
v___x_1696_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2___redArg(v___x_1692_, v_data_1688_, v___x_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(lean_object* v_a_1697_, lean_object* v_x_1698_){
_start:
{
if (lean_obj_tag(v_x_1698_) == 0)
{
uint8_t v___x_1699_; 
v___x_1699_ = 0;
return v___x_1699_;
}
else
{
lean_object* v_key_1700_; lean_object* v_tail_1701_; uint8_t v___x_1702_; 
v_key_1700_ = lean_ctor_get(v_x_1698_, 0);
v_tail_1701_ = lean_ctor_get(v_x_1698_, 2);
v___x_1702_ = lean_name_eq(v_key_1700_, v_a_1697_);
if (v___x_1702_ == 0)
{
v_x_1698_ = v_tail_1701_;
goto _start;
}
else
{
return v___x_1702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_1704_, lean_object* v_x_1705_){
_start:
{
uint8_t v_res_1706_; lean_object* v_r_1707_; 
v_res_1706_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(v_a_1704_, v_x_1705_);
lean_dec(v_x_1705_);
lean_dec(v_a_1704_);
v_r_1707_ = lean_box(v_res_1706_);
return v_r_1707_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0___redArg(lean_object* v_m_1708_, lean_object* v_a_1709_, lean_object* v_b_1710_){
_start:
{
lean_object* v_size_1711_; lean_object* v_buckets_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1758_; 
v_size_1711_ = lean_ctor_get(v_m_1708_, 0);
v_buckets_1712_ = lean_ctor_get(v_m_1708_, 1);
v_isSharedCheck_1758_ = !lean_is_exclusive(v_m_1708_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1714_ = v_m_1708_;
v_isShared_1715_ = v_isSharedCheck_1758_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_buckets_1712_);
lean_inc(v_size_1711_);
lean_dec(v_m_1708_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1758_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; uint64_t v___y_1718_; 
v___x_1716_ = lean_array_get_size(v_buckets_1712_);
if (lean_obj_tag(v_a_1709_) == 0)
{
uint64_t v___x_1756_; 
v___x_1756_ = 1723ULL;
v___y_1718_ = v___x_1756_;
goto v___jp_1717_;
}
else
{
uint64_t v_hash_1757_; 
v_hash_1757_ = lean_ctor_get_uint64(v_a_1709_, sizeof(void*)*2);
v___y_1718_ = v_hash_1757_;
goto v___jp_1717_;
}
v___jp_1717_:
{
uint64_t v___x_1719_; uint64_t v___x_1720_; uint64_t v_fold_1721_; uint64_t v___x_1722_; uint64_t v___x_1723_; uint64_t v___x_1724_; size_t v___x_1725_; size_t v___x_1726_; size_t v___x_1727_; size_t v___x_1728_; size_t v___x_1729_; lean_object* v_bkt_1730_; uint8_t v___x_1731_; 
v___x_1719_ = 32ULL;
v___x_1720_ = lean_uint64_shift_right(v___y_1718_, v___x_1719_);
v_fold_1721_ = lean_uint64_xor(v___y_1718_, v___x_1720_);
v___x_1722_ = 16ULL;
v___x_1723_ = lean_uint64_shift_right(v_fold_1721_, v___x_1722_);
v___x_1724_ = lean_uint64_xor(v_fold_1721_, v___x_1723_);
v___x_1725_ = lean_uint64_to_usize(v___x_1724_);
v___x_1726_ = lean_usize_of_nat(v___x_1716_);
v___x_1727_ = ((size_t)1ULL);
v___x_1728_ = lean_usize_sub(v___x_1726_, v___x_1727_);
v___x_1729_ = lean_usize_land(v___x_1725_, v___x_1728_);
v_bkt_1730_ = lean_array_uget_borrowed(v_buckets_1712_, v___x_1729_);
v___x_1731_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(v_a_1709_, v_bkt_1730_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v_size_x27_1733_; lean_object* v___x_1734_; lean_object* v_buckets_x27_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; uint8_t v___x_1741_; 
v___x_1732_ = lean_unsigned_to_nat(1u);
v_size_x27_1733_ = lean_nat_add(v_size_1711_, v___x_1732_);
lean_dec(v_size_1711_);
lean_inc(v_bkt_1730_);
v___x_1734_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1734_, 0, v_a_1709_);
lean_ctor_set(v___x_1734_, 1, v_b_1710_);
lean_ctor_set(v___x_1734_, 2, v_bkt_1730_);
v_buckets_x27_1735_ = lean_array_uset(v_buckets_1712_, v___x_1729_, v___x_1734_);
v___x_1736_ = lean_unsigned_to_nat(4u);
v___x_1737_ = lean_nat_mul(v_size_x27_1733_, v___x_1736_);
v___x_1738_ = lean_unsigned_to_nat(3u);
v___x_1739_ = lean_nat_div(v___x_1737_, v___x_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_array_get_size(v_buckets_x27_1735_);
v___x_1741_ = lean_nat_dec_le(v___x_1739_, v___x_1740_);
lean_dec(v___x_1739_);
if (v___x_1741_ == 0)
{
lean_object* v_val_1742_; lean_object* v___x_1744_; 
v_val_1742_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1___redArg(v_buckets_x27_1735_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 1, v_val_1742_);
lean_ctor_set(v___x_1714_, 0, v_size_x27_1733_);
v___x_1744_ = v___x_1714_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_size_x27_1733_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_val_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
else
{
lean_object* v___x_1747_; 
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 1, v_buckets_x27_1735_);
lean_ctor_set(v___x_1714_, 0, v_size_x27_1733_);
v___x_1747_ = v___x_1714_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_size_x27_1733_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v_buckets_x27_1735_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
else
{
lean_object* v___x_1749_; lean_object* v_buckets_x27_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1754_; 
lean_inc(v_bkt_1730_);
v___x_1749_ = lean_box(0);
v_buckets_x27_1750_ = lean_array_uset(v_buckets_1712_, v___x_1729_, v___x_1749_);
v___x_1751_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2___redArg(v_a_1709_, v_b_1710_, v_bkt_1730_);
v___x_1752_ = lean_array_uset(v_buckets_x27_1750_, v___x_1729_, v___x_1751_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 1, v___x_1752_);
v___x_1754_ = v___x_1714_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_size_1711_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v___x_1752_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerSimpAttr(lean_object* v_attrName_1759_, lean_object* v_attrDescr_1760_, lean_object* v_ref_1761_){
_start:
{
lean_object* v___x_1763_; 
lean_inc(v_ref_1761_);
v___x_1763_ = l_Lean_Meta_mkSimpExt(v_ref_1761_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1765_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc_n(v_a_1764_, 2);
lean_dec_ref_known(v___x_1763_, 1);
lean_inc(v_attrName_1759_);
v___x_1765_ = l_Lean_Meta_mkSimpAttr(v_attrName_1759_, v_attrDescr_1760_, v_a_1764_, v_ref_1761_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1776_; 
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1776_ == 0)
{
lean_object* v_unused_1777_; 
v_unused_1777_ = lean_ctor_get(v___x_1765_, 0);
lean_dec(v_unused_1777_);
v___x_1767_ = v___x_1765_;
v_isShared_1768_ = v_isSharedCheck_1776_;
goto v_resetjp_1766_;
}
else
{
lean_dec(v___x_1765_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1776_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1769_ = l_Lean_Meta_simpExtensionMapRef;
v___x_1770_ = lean_st_ref_take(v___x_1769_);
lean_inc(v_a_1764_);
v___x_1771_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0___redArg(v___x_1770_, v_attrName_1759_, v_a_1764_);
v___x_1772_ = lean_st_ref_put(v___x_1769_, v___x_1771_);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v_a_1764_);
v___x_1774_ = v___x_1767_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1764_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_dec(v_a_1764_);
lean_dec(v_attrName_1759_);
v_a_1778_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1765_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1765_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
else
{
lean_dec(v_ref_1761_);
lean_dec_ref(v_attrDescr_1760_);
lean_dec(v_attrName_1759_);
return v___x_1763_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerSimpAttr___boxed(lean_object* v_attrName_1786_, lean_object* v_attrDescr_1787_, lean_object* v_ref_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_Meta_registerSimpAttr(v_attrName_1786_, v_attrDescr_1787_, v_ref_1788_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0(lean_object* v_00_u03b2_1791_, lean_object* v_m_1792_, lean_object* v_a_1793_, lean_object* v_b_1794_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0___redArg(v_m_1792_, v_a_1793_, v_b_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0(lean_object* v_00_u03b2_1796_, lean_object* v_a_1797_, lean_object* v_x_1798_){
_start:
{
uint8_t v___x_1799_; 
v___x_1799_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___redArg(v_a_1797_, v_x_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1800_, lean_object* v_a_1801_, lean_object* v_x_1802_){
_start:
{
uint8_t v_res_1803_; lean_object* v_r_1804_; 
v_res_1803_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__0(v_00_u03b2_1800_, v_a_1801_, v_x_1802_);
lean_dec(v_x_1802_);
lean_dec(v_a_1801_);
v_r_1804_ = lean_box(v_res_1803_);
return v_r_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1(lean_object* v_00_u03b2_1805_, lean_object* v_data_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1___redArg(v_data_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2(lean_object* v_00_u03b2_1808_, lean_object* v_a_1809_, lean_object* v_b_1810_, lean_object* v_x_1811_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__2___redArg(v_a_1809_, v_b_1810_, v_x_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1813_, lean_object* v_i_1814_, lean_object* v_source_1815_, lean_object* v_target_1816_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2___redArg(v_i_1814_, v_source_1815_, v_target_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1818_, lean_object* v_x_1819_, lean_object* v_x_1820_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_registerSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1819_, v_x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1833_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_));
v___x_1834_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_));
v___x_1835_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_));
v___x_1836_ = l_Lean_Meta_registerSimpAttr(v___x_1833_, v___x_1834_, v___x_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2____boxed(lean_object* v_a_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_3725168437____hygCtx___hyg_2_();
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1849_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_));
v___x_1850_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_));
v___x_1851_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_));
v___x_1852_ = l_Lean_Meta_registerSimpAttr(v___x_1849_, v___x_1850_, v___x_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2____boxed(lean_object* v_a_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l___private_Lean_Meta_Tactic_Simp_Attr_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_Attr_1436443379____hygCtx___hyg_2_();
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___redArg(lean_object* v_a_1855_){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = l_Lean_Meta_simpExtension;
v___x_1858_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_1857_, v_a_1855_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___redArg___boxed(lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_1859_);
lean_dec(v_a_1859_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems(lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_1863_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_Meta_getSimpTheorems(v_a_1866_, v_a_1867_);
lean_dec(v_a_1867_);
lean_dec_ref(v_a_1866_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___redArg(lean_object* v_a_1870_){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = l_Lean_Meta_sevalSimpExtension;
v___x_1873_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_1872_, v_a_1870_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___redArg___boxed(lean_object* v_a_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_Meta_getSEvalTheorems___redArg(v_a_1874_);
lean_dec(v_a_1874_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems(lean_object* v_a_1877_, lean_object* v_a_1878_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Lean_Meta_getSEvalTheorems___redArg(v_a_1878_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___boxed(lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_Meta_getSEvalTheorems(v_a_1881_, v_a_1882_);
lean_dec(v_a_1882_);
lean_dec_ref(v_a_1881_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___redArg(lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_1894_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1898_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
lean_dec_ref_known(v___x_1896_, 1);
v___x_1898_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1894_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v___x_1898_, 1);
v___x_1900_ = ((lean_object*)(l_Lean_Meta_Simp_Context_mkDefault___redArg___closed__0));
v___x_1901_ = lean_unsigned_to_nat(1u);
v___x_1902_ = lean_mk_empty_array_with_capacity(v___x_1901_);
v___x_1903_ = lean_array_push(v___x_1902_, v_a_1897_);
v___x_1904_ = l_Lean_Options_empty;
v___x_1905_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1900_, v___x_1903_, v_a_1899_, v___x_1904_, v_a_1892_, v_a_1893_, v_a_1894_);
return v___x_1905_;
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_dec(v_a_1897_);
v_a_1906_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1898_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1898_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
v_a_1914_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1896_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1896_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___redArg___boxed(lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Lean_Meta_Simp_Context_mkDefault___redArg(v_a_1922_, v_a_1923_, v_a_1924_);
lean_dec(v_a_1924_);
lean_dec_ref(v_a_1923_);
lean_dec_ref(v_a_1922_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault(lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = l_Lean_Meta_Simp_Context_mkDefault___redArg(v_a_1927_, v_a_1929_, v_a_1930_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___boxed(lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_Meta_Simp_Context_mkDefault(v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
lean_dec(v_a_1936_);
lean_dec_ref(v_a_1935_);
lean_dec(v_a_1934_);
lean_dec_ref(v_a_1933_);
return v_res_1938_;
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
