// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide
// Imports: public import Lean.Meta.Tactic.BVDecide.Main public import Lean.Meta.Tactic.TryThis import Lean.Meta.Tactic.BVDecide.TacticContext import Lean.Meta.Tactic.BVDecide.Normalize import Lean.Meta.Tactic.BVDecide.LRAT.Trim import Lean.Meta.Sym.Util import Lean.Meta.Tactic.Grind.Main
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
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdx_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkDefaultParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_GrindM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(lean_object*);
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_MVarId_assertHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_M_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_fileName(lean_object*);
lean_object* l_Lean_Elab_Term_getDeclName_x3f___redArg(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_remove_file(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_LRAT_trim(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_create_tempfile();
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "to use `bv_decide`, please include `import Std.Tactic.BVDecide`"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "cannot compute parent directory of `"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6;
static const lean_array_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ".lrat"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "could not find declaration name"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "could not find file name"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_normalize_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_normalize_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_check_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_check_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "bvDecide"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(50, 136, 47, 200, 127, 182, 157, 78)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvTypes"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6_value),LEAN_SCALAR_PTR_LITERAL(133, 159, 97, 61, 240, 205, 127, 31)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalBvDecide"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(254, 33, 71, 133, 230, 185, 178, 141)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "bvNormalize"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "bv_normalize"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvCheck"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "bv_check"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvTrace"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 230, 11, 166, 96, 155, 151, 146)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "evalBvTraceTactic"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 218, 116, 146, 170, 4, 165, 61)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___boxed(lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__5_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "This goal can be closed by only applying bv_normalize, no need to keep the LRAT proof around."};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(237, 160, 246, 114, 147, 242, 134, 91)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "evalBvCheckTactic"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 96, 81, 97, 114, 57, 143, 106)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(240, 99, 199, 244, 147, 253, 171, 138)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "evalBVNormalize"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 145, 175, 22, 183, 69, 214, 22)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___boxed(lean_object*);
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__1);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_5_);
lean_ctor_set(v___x_6_, 2, v___x_5_);
lean_ctor_set(v___x_6_, 3, v___x_5_);
lean_ctor_set(v___x_6_, 4, v___x_4_);
lean_ctor_set(v___x_6_, 5, v___x_4_);
lean_ctor_set(v___x_6_, 6, v___x_4_);
lean_ctor_set(v___x_6_, 7, v___x_4_);
lean_ctor_set(v___x_6_, 8, v___x_4_);
lean_ctor_set(v___x_6_, 9, v___x_4_);
lean_ctor_set(v___x_6_, 10, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = lean_unsigned_to_nat(32u);
v___x_8_ = lean_mk_empty_array_with_capacity(v___x_7_);
v___x_9_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_10_ = ((size_t)5ULL);
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lean_unsigned_to_nat(32u);
v___x_13_ = lean_mk_empty_array_with_capacity(v___x_12_);
v___x_14_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__3);
v___x_15_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v___x_13_);
lean_ctor_set(v___x_15_, 2, v___x_11_);
lean_ctor_set(v___x_15_, 3, v___x_11_);
lean_ctor_set_usize(v___x_15_, 4, v___x_10_);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_16_ = lean_box(1);
v___x_17_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__4);
v___x_18_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__1);
v___x_19_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___x_17_);
lean_ctor_set(v___x_19_, 2, v___x_16_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0(lean_object* v_msgData_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v___x_24_; lean_object* v_env_25_; lean_object* v_options_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_24_ = lean_st_ref_get(v___y_22_);
v_env_25_ = lean_ctor_get(v___x_24_, 0);
lean_inc_ref(v_env_25_);
lean_dec(v___x_24_);
v_options_26_ = lean_ctor_get(v___y_21_, 2);
v___x_27_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__2);
v___x_28_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_26_);
v___x_29_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_29_, 0, v_env_25_);
lean_ctor_set(v___x_29_, 1, v___x_27_);
lean_ctor_set(v___x_29_, 2, v___x_28_);
lean_ctor_set(v___x_29_, 3, v_options_26_);
v___x_30_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
lean_ctor_set(v___x_30_, 1, v_msgData_20_);
v___x_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___boxed(lean_object* v_msgData_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0(v_msgData_32_, v___y_33_, v___y_34_);
lean_dec(v___y_34_);
lean_dec_ref(v___y_33_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg(lean_object* v_msg_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v_ref_41_; lean_object* v___x_42_; lean_object* v_a_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_51_; 
v_ref_41_ = lean_ctor_get(v___y_38_, 5);
v___x_42_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0(v_msg_37_, v___y_38_, v___y_39_);
v_a_43_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_51_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_51_ == 0)
{
v___x_45_ = v___x_42_;
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_a_43_);
lean_dec(v___x_42_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_47_; lean_object* v___x_49_; 
lean_inc(v_ref_41_);
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v_ref_41_);
lean_ctor_set(v___x_47_, 1, v_a_43_);
if (v_isShared_46_ == 0)
{
lean_ctor_set_tag(v___x_45_, 1);
lean_ctor_set(v___x_45_, 0, v___x_47_);
v___x_49_ = v___x_45_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_47_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg___boxed(lean_object* v_msg_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg(v_msg_52_, v___y_53_, v___y_54_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
return v_res_56_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__5(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__4));
v___x_66_ = l_Lean_stringToMessageData(v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v___x_70_; lean_object* v_env_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_70_ = lean_st_ref_get(v_a_68_);
v_env_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc_ref(v_env_71_);
lean_dec(v___x_70_);
v___x_72_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__3));
v___x_73_ = l_Lean_Environment_getModuleIdx_x3f(v_env_71_, v___x_72_);
lean_dec_ref(v_env_71_);
if (lean_obj_tag(v___x_73_) == 0)
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__5, &l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__5);
v___x_75_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg(v___x_74_, v_a_67_, v_a_68_);
return v___x_75_;
}
else
{
lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_83_; 
v_isSharedCheck_83_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_83_ == 0)
{
lean_object* v_unused_84_; 
v_unused_84_ = lean_ctor_get(v___x_73_, 0);
lean_dec(v_unused_84_);
v___x_77_ = v___x_73_;
v_isShared_78_ = v_isSharedCheck_83_;
goto v_resetjp_76_;
}
else
{
lean_dec(v___x_73_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_83_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_79_; lean_object* v___x_81_; 
v___x_79_ = lean_box(0);
if (v_isShared_78_ == 0)
{
lean_ctor_set_tag(v___x_77_, 0);
lean_ctor_set(v___x_77_, 0, v___x_79_);
v___x_81_ = v___x_77_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_79_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___boxed(lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v_a_85_, v_a_86_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0(lean_object* v_00_u03b1_89_, lean_object* v_msg_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg(v_msg_90_, v___y_91_, v___y_92_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___boxed(lean_object* v_00_u03b1_95_, lean_object* v_msg_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0(v_00_u03b1_95_, v_msg_96_, v___y_97_, v___y_98_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(lean_object* v_msgData_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0___boxed(lean_object* v_msgData_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v_msgData_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
return v_res_122_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_box(1);
v___x_124_ = l_Lean_MessageData_ofFormat(v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__2));
v___x_129_ = l_Lean_MessageData_ofFormat(v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3(lean_object* v_x_130_, lean_object* v_x_131_){
_start:
{
if (lean_obj_tag(v_x_131_) == 0)
{
return v_x_130_;
}
else
{
lean_object* v_head_132_; lean_object* v_tail_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_155_; 
v_head_132_ = lean_ctor_get(v_x_131_, 0);
v_tail_133_ = lean_ctor_get(v_x_131_, 1);
v_isSharedCheck_155_ = !lean_is_exclusive(v_x_131_);
if (v_isSharedCheck_155_ == 0)
{
v___x_135_ = v_x_131_;
v_isShared_136_ = v_isSharedCheck_155_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_tail_133_);
lean_inc(v_head_132_);
lean_dec(v_x_131_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_155_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v_before_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_153_; 
v_before_137_ = lean_ctor_get(v_head_132_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v_head_132_);
if (v_isSharedCheck_153_ == 0)
{
lean_object* v_unused_154_; 
v_unused_154_ = lean_ctor_get(v_head_132_, 1);
lean_dec(v_unused_154_);
v___x_139_ = v_head_132_;
v_isShared_140_ = v_isSharedCheck_153_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_before_137_);
lean_dec(v_head_132_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_153_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_141_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_140_ == 0)
{
lean_ctor_set_tag(v___x_139_, 7);
lean_ctor_set(v___x_139_, 1, v___x_141_);
lean_ctor_set(v___x_139_, 0, v_x_130_);
v___x_143_ = v___x_139_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_x_130_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v___x_141_);
v___x_143_ = v_reuseFailAlloc_152_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_144_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_136_ == 0)
{
lean_ctor_set_tag(v___x_135_, 7);
lean_ctor_set(v___x_135_, 1, v___x_144_);
lean_ctor_set(v___x_135_, 0, v___x_143_);
v___x_146_ = v___x_135_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_143_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v___x_144_);
v___x_146_ = v_reuseFailAlloc_151_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = l_Lean_MessageData_ofSyntax(v_before_137_);
v___x_148_ = l_Lean_indentD(v___x_147_);
v___x_149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_146_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
v_x_130_ = v___x_149_;
v_x_131_ = v_tail_133_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(lean_object* v_opts_156_, lean_object* v_opt_157_){
_start:
{
lean_object* v_name_158_; lean_object* v_defValue_159_; lean_object* v_map_160_; lean_object* v___x_161_; 
v_name_158_ = lean_ctor_get(v_opt_157_, 0);
v_defValue_159_ = lean_ctor_get(v_opt_157_, 1);
v_map_160_ = lean_ctor_get(v_opts_156_, 0);
v___x_161_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_160_, v_name_158_);
if (lean_obj_tag(v___x_161_) == 0)
{
uint8_t v___x_162_; 
v___x_162_ = lean_unbox(v_defValue_159_);
return v___x_162_;
}
else
{
lean_object* v_val_163_; 
v_val_163_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_val_163_);
lean_dec_ref_known(v___x_161_, 1);
if (lean_obj_tag(v_val_163_) == 1)
{
uint8_t v_v_164_; 
v_v_164_ = lean_ctor_get_uint8(v_val_163_, 0);
lean_dec_ref_known(v_val_163_, 0);
return v_v_164_;
}
else
{
uint8_t v___x_165_; 
lean_dec(v_val_163_);
v___x_165_ = lean_unbox(v_defValue_159_);
return v___x_165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_166_, lean_object* v_opt_167_){
_start:
{
uint8_t v_res_168_; lean_object* v_r_169_; 
v_res_168_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_opts_166_, v_opt_167_);
lean_dec_ref(v_opt_167_);
lean_dec_ref(v_opts_166_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__1));
v___x_174_ = l_Lean_MessageData_ofFormat(v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(lean_object* v_msgData_175_, lean_object* v_macroStack_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_options_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v_options_179_ = lean_ctor_get(v___y_177_, 2);
v___x_180_ = l_Lean_Elab_pp_macroStack;
v___x_181_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_179_, v___x_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
lean_dec(v_macroStack_176_);
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v_msgData_175_);
return v___x_182_;
}
else
{
if (lean_obj_tag(v_macroStack_176_) == 0)
{
lean_object* v___x_183_; 
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v_msgData_175_);
return v___x_183_;
}
else
{
lean_object* v_head_184_; lean_object* v_after_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_200_; 
v_head_184_ = lean_ctor_get(v_macroStack_176_, 0);
lean_inc(v_head_184_);
v_after_185_ = lean_ctor_get(v_head_184_, 1);
v_isSharedCheck_200_ = !lean_is_exclusive(v_head_184_);
if (v_isSharedCheck_200_ == 0)
{
lean_object* v_unused_201_; 
v_unused_201_ = lean_ctor_get(v_head_184_, 0);
lean_dec(v_unused_201_);
v___x_187_ = v_head_184_;
v_isShared_188_ = v_isSharedCheck_200_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_after_185_);
lean_dec(v_head_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_200_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_189_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_188_ == 0)
{
lean_ctor_set_tag(v___x_187_, 7);
lean_ctor_set(v___x_187_, 1, v___x_189_);
lean_ctor_set(v___x_187_, 0, v_msgData_175_);
v___x_191_ = v___x_187_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_msgData_175_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v___x_189_);
v___x_191_ = v_reuseFailAlloc_199_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v_msgData_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_192_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2);
v___x_193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_191_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v___x_194_ = l_Lean_MessageData_ofSyntax(v_after_185_);
v___x_195_ = l_Lean_indentD(v___x_194_);
v_msgData_196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_196_, 0, v___x_193_);
lean_ctor_set(v_msgData_196_, 1, v___x_195_);
v___x_197_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3(v_msgData_196_, v_macroStack_176_);
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
return v___x_198_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_202_, lean_object* v_macroStack_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_msgData_202_, v_macroStack_203_, v___y_204_);
lean_dec_ref(v___y_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(lean_object* v_msg_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_ref_215_; lean_object* v___x_216_; lean_object* v_a_217_; lean_object* v_macroStack_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_229_; 
v_ref_215_ = lean_ctor_get(v___y_212_, 5);
v___x_216_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v_msg_207_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
v_a_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_a_217_);
lean_dec_ref(v___x_216_);
v_macroStack_218_ = lean_ctor_get(v___y_208_, 1);
v___x_219_ = l_Lean_Elab_getBetterRef(v_ref_215_, v_macroStack_218_);
lean_inc(v_macroStack_218_);
v___x_220_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_a_217_, v_macroStack_218_, v___y_212_);
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
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_219_);
lean_ctor_set(v___x_225_, 1, v_a_221_);
if (v_isShared_224_ == 0)
{
lean_ctor_set_tag(v___x_223_, 1);
lean_ctor_set(v___x_223_, 0, v___x_225_);
v___x_227_ = v___x_223_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
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
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg___boxed(lean_object* v_msg_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v_msg_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
return v_res_238_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__0));
v___x_241_ = l_Lean_stringToMessageData(v___x_240_);
return v___x_241_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__2));
v___x_244_ = l_Lean_stringToMessageData(v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_fileName_252_; lean_object* v___x_253_; 
v_fileName_252_ = lean_ctor_get(v_a_249_, 0);
lean_inc_ref(v_fileName_252_);
v___x_253_ = l_System_FilePath_parent(v_fileName_252_);
if (lean_obj_tag(v___x_253_) == 1)
{
lean_object* v_val_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
v_val_254_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_253_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_val_254_);
lean_dec(v___x_253_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
lean_ctor_set_tag(v___x_256_, 0);
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_val_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec(v___x_253_);
v___x_262_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1, &l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1);
lean_inc_ref(v_fileName_252_);
v___x_263_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_263_, 0, v_fileName_252_);
v___x_264_ = l_Lean_MessageData_ofFormat(v___x_263_);
v___x_265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_262_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3, &l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3);
v___x_267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v___x_267_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_);
return v___x_268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___boxed(lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0(lean_object* v_00_u03b1_277_, lean_object* v_msg_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v_msg_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___boxed(lean_object* v_00_u03b1_287_, lean_object* v_msg_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0(v_00_u03b1_287_, v_msg_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1(lean_object* v_msgData_297_, lean_object* v_macroStack_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_msgData_297_, v_macroStack_298_, v___y_303_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___boxed(lean_object* v_msgData_307_, lean_object* v_macroStack_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1(v_msgData_307_, v_macroStack_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(lean_object* v_lratPath_317_, lean_object* v_cfg_318_, lean_object* v_types_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_a_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_a_328_);
lean_dec_ref_known(v___x_327_, 1);
v___x_329_ = l_System_FilePath_join(v_a_328_, v_lratPath_317_);
v___x_330_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new(v___x_329_, v_cfg_318_, v_types_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
return v___x_330_;
}
else
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_dec(v_types_319_);
lean_dec_ref(v_cfg_318_);
lean_dec_ref(v_lratPath_317_);
v_a_331_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_327_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_327_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext___boxed(lean_object* v_lratPath_339_, lean_object* v_cfg_340_, lean_object* v_types_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v_lratPath_339_, v_cfg_340_, v_types_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0(lean_object* v_g_350_, lean_object* v___x_351_, lean_object* v___x_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(v_g_350_, v___x_351_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; 
v_unused_370_ = lean_ctor_get(v___x_362_, 0);
lean_dec(v_unused_370_);
v___x_364_ = v___x_362_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_dec(v___x_362_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_352_);
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_352_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
v_a_371_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_362_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_362_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0___boxed(lean_object* v_g_379_, lean_object* v___x_380_, lean_object* v___x_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0(v_g_379_, v___x_380_, v___x_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(lean_object* v_g_392_, lean_object* v_hypotheses_393_, lean_object* v_ctx_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___f_404_; lean_object* v___x_405_; 
v___x_402_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed), 9, 1);
lean_closure_set(v___x_402_, 0, v_ctx_394_);
v___x_403_ = lean_box(0);
v___f_404_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0___boxed), 12, 3);
lean_closure_set(v___f_404_, 0, v_g_392_);
lean_closure_set(v___f_404_, 1, v___x_402_);
lean_closure_set(v___f_404_, 2, v___x_403_);
v___x_405_ = l_Lean_Meta_Tactic_BVDecide_M_run___redArg(v___f_404_, v_hypotheses_393_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___boxed(lean_object* v_g_406_, lean_object* v_hypotheses_407_, lean_object* v_ctx_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(v_g_406_, v_hypotheses_407_, v_ctx_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
return v_res_416_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0(void){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_417_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
return v___x_419_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1);
v___x_421_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
lean_ctor_set(v___x_421_, 2, v___x_420_);
lean_ctor_set(v___x_421_, 3, v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3(void){
_start:
{
lean_object* v_cellCount_422_; lean_object* v___x_423_; 
v_cellCount_422_ = lean_unsigned_to_nat(16u);
v___x_423_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_422_);
return v___x_423_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4(void){
_start:
{
lean_object* v_cellCount_424_; lean_object* v___x_425_; 
v_cellCount_424_ = lean_unsigned_to_nat(16u);
v___x_425_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_424_);
return v___x_425_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_426_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4);
v___x_427_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3);
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_429_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v___x_427_);
lean_ctor_set(v___x_429_, 2, v___x_426_);
return v___x_429_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5);
v___x_431_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
lean_ctor_set(v___x_431_, 2, v___x_430_);
lean_ctor_set(v___x_431_, 3, v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck(lean_object* v_target_434_, lean_object* v_ctx_435_, lean_object* v_warn_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___y_454_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_447_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2);
v___x_448_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6);
v___x_449_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__7));
v___x_450_ = 0;
v___x_451_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_451_, 0, v___x_447_);
lean_ctor_set(v___x_451_, 1, v___x_448_);
lean_ctor_set(v___x_451_, 2, v_target_434_);
lean_ctor_set(v___x_451_, 3, v___x_449_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*4, v___x_450_);
v___x_452_ = lean_st_mk_ref(v___x_451_);
lean_inc_ref(v_ctx_435_);
v___x_464_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_ctx_435_);
v___x_465_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_464_, v___x_452_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
lean_dec_ref(v___x_464_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; uint8_t v___x_467_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_a_466_);
lean_dec_ref_known(v___x_465_, 1);
v___x_467_ = lean_unbox(v_a_466_);
lean_dec(v_a_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v_target_470_; lean_object* v_hypotheses_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
lean_dec_ref(v_warn_436_);
v___x_468_ = lean_st_ref_get(v___x_452_);
v___x_469_ = lean_st_ref_get(v___x_452_);
v_target_470_ = lean_ctor_get(v___x_468_, 2);
lean_inc_ref(v_target_470_);
lean_dec(v___x_468_);
v_hypotheses_471_ = lean_ctor_get(v___x_469_, 3);
lean_inc_ref(v_hypotheses_471_);
lean_dec(v___x_469_);
v___x_472_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_470_);
lean_dec_ref(v_target_470_);
v___x_473_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(v___x_472_, v_hypotheses_471_, v_ctx_435_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
v___y_454_ = v___x_473_;
goto v___jp_453_;
}
else
{
lean_object* v___x_474_; 
lean_dec_ref(v_ctx_435_);
lean_inc(v_a_445_);
lean_inc_ref(v_a_444_);
lean_inc(v_a_443_);
lean_inc_ref(v_a_442_);
v___x_474_ = lean_apply_5(v_warn_436_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, lean_box(0));
v___y_454_ = v___x_474_;
goto v___jp_453_;
}
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec(v___x_452_);
lean_dec_ref(v_warn_436_);
lean_dec_ref(v_ctx_435_);
v_a_475_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_465_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_465_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
v___jp_453_:
{
if (lean_obj_tag(v___y_454_) == 0)
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_463_; 
v_a_455_ = lean_ctor_get(v___y_454_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___y_454_);
if (v_isSharedCheck_463_ == 0)
{
v___x_457_ = v___y_454_;
v_isShared_458_ = v_isSharedCheck_463_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___y_454_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_463_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_459_ = lean_st_ref_get(v___x_452_);
lean_dec(v___x_452_);
lean_dec(v___x_459_);
if (v_isShared_458_ == 0)
{
v___x_461_ = v___x_457_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_455_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
else
{
lean_dec(v___x_452_);
return v___y_454_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed(lean_object* v_target_483_, lean_object* v_ctx_484_, lean_object* v_warn_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck(v_target_483_, v_ctx_484_, v_warn_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(lean_object* v___y_497_){
_start:
{
lean_object* v_ref_499_; uint8_t v___x_500_; lean_object* v___x_501_; 
v_ref_499_ = lean_ctor_get(v___y_497_, 5);
v___x_500_ = 0;
v___x_501_ = l_Lean_Syntax_getPos_x3f(v_ref_499_, v___x_500_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_unsigned_to_nat(0u);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
else
{
lean_object* v_val_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
v_val_504_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_501_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_val_504_);
lean_dec(v___x_501_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set_tag(v___x_506_, 0);
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_val_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg___boxed(lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v___y_512_);
lean_dec_ref(v___y_512_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0(lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v___y_519_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___boxed(lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0(v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
return v_res_530_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__2));
v___x_535_ = l_Lean_stringToMessageData(v___x_534_);
return v___x_535_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__4));
v___x_538_ = l_Lean_stringToMessageData(v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
lean_object* v_fileName_546_; lean_object* v_fileMap_547_; lean_object* v___x_548_; 
v_fileName_546_ = lean_ctor_get(v_a_543_, 0);
v_fileMap_547_ = lean_ctor_get(v_a_543_, 1);
lean_inc_ref(v_fileName_546_);
v___x_548_ = l_System_FilePath_fileName(v_fileName_546_);
if (lean_obj_tag(v___x_548_) == 1)
{
lean_object* v_val_549_; lean_object* v___x_550_; 
v_val_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_val_549_);
lean_dec_ref_known(v___x_548_, 1);
v___x_550_ = l_Lean_Elab_Term_getDeclName_x3f___redArg(v_a_539_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_550_, 1);
if (lean_obj_tag(v_a_551_) == 1)
{
lean_object* v_val_552_; lean_object* v___x_553_; lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_577_; 
v_val_552_ = lean_ctor_get(v_a_551_, 0);
lean_inc(v_val_552_);
lean_dec_ref_known(v_a_551_, 1);
v___x_553_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v_a_543_);
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_577_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_577_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_577_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v_line_559_; lean_object* v_column_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
lean_inc_ref(v_fileMap_547_);
v___x_558_ = l_Lean_FileMap_toPosition(v_fileMap_547_, v_a_554_);
lean_dec(v_a_554_);
v_line_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_line_559_);
v_column_560_ = lean_ctor_get(v___x_558_, 1);
lean_inc(v_column_560_);
lean_dec_ref(v___x_558_);
v___x_561_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__0));
v___x_562_ = lean_string_append(v_val_549_, v___x_561_);
v___x_563_ = 1;
v___x_564_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_552_, v___x_563_);
v___x_565_ = lean_string_append(v___x_562_, v___x_564_);
lean_dec_ref(v___x_564_);
v___x_566_ = lean_string_append(v___x_565_, v___x_561_);
v___x_567_ = l_Nat_reprFast(v_line_559_);
v___x_568_ = lean_string_append(v___x_566_, v___x_567_);
lean_dec_ref(v___x_567_);
v___x_569_ = lean_string_append(v___x_568_, v___x_561_);
v___x_570_ = l_Nat_reprFast(v_column_560_);
v___x_571_ = lean_string_append(v___x_569_, v___x_570_);
lean_dec_ref(v___x_570_);
v___x_572_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__1));
v___x_573_ = lean_string_append(v___x_571_, v___x_572_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_573_);
v___x_575_ = v___x_556_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v_a_551_);
lean_dec(v_val_549_);
v___x_578_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3, &l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3);
v___x_579_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v___x_578_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
return v___x_579_;
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec(v_val_549_);
v_a_580_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_550_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_550_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; 
lean_dec(v___x_548_);
v___x_588_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5, &l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5);
v___x_589_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v___x_588_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
return v___x_589_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___boxed(lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(lean_object* v_cfg_598_, lean_object* v_types_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_609_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_607_, 1);
v___x_609_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v_a_608_, v_cfg_598_, v_types_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
return v___x_609_;
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec(v_types_599_);
lean_dec_ref(v_cfg_598_);
v_a_610_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_607_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_607_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext___boxed(lean_object* v_cfg_618_, lean_object* v_types_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(v_cfg_618_, v_types_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorIdx(lean_object* v_x_628_){
_start:
{
if (lean_obj_tag(v_x_628_) == 0)
{
lean_object* v___x_629_; 
v___x_629_ = lean_unsigned_to_nat(0u);
return v___x_629_;
}
else
{
lean_object* v___x_630_; 
v___x_630_ = lean_unsigned_to_nat(1u);
return v___x_630_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorIdx___boxed(lean_object* v_x_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorIdx(v_x_631_);
lean_dec(v_x_631_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(lean_object* v_t_633_, lean_object* v_k_634_){
_start:
{
if (lean_obj_tag(v_t_633_) == 0)
{
return v_k_634_;
}
else
{
lean_object* v_path_635_; lean_object* v___x_636_; 
v_path_635_ = lean_ctor_get(v_t_633_, 0);
lean_inc_ref(v_path_635_);
lean_dec_ref_known(v_t_633_, 1);
v___x_636_ = lean_apply_1(v_k_634_, v_path_635_);
return v___x_636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim(lean_object* v_motive_637_, lean_object* v_ctorIdx_638_, lean_object* v_t_639_, lean_object* v_h_640_, lean_object* v_k_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_639_, v_k_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___boxed(lean_object* v_motive_643_, lean_object* v_ctorIdx_644_, lean_object* v_t_645_, lean_object* v_h_646_, lean_object* v_k_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim(v_motive_643_, v_ctorIdx_644_, v_t_645_, v_h_646_, v_k_647_);
lean_dec(v_ctorIdx_644_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_normalize_elim___redArg(lean_object* v_t_649_, lean_object* v_normalize_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_649_, v_normalize_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_normalize_elim(lean_object* v_motive_652_, lean_object* v_t_653_, lean_object* v_h_654_, lean_object* v_normalize_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_653_, v_normalize_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_check_elim___redArg(lean_object* v_t_657_, lean_object* v_check_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_657_, v_check_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_check_elim(lean_object* v_motive_660_, lean_object* v_t_661_, lean_object* v_h_662_, lean_object* v_check_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_661_, v_check_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0(lean_object* v_x_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v___x_676_; 
lean_inc(v___y_670_);
lean_inc_ref(v___y_669_);
lean_inc(v___y_668_);
lean_inc_ref(v___y_667_);
lean_inc(v___y_666_);
v___x_676_ = lean_apply_10(v_x_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, lean_box(0));
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0___boxed(lean_object* v_x_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0(v_x_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(lean_object* v_mvarId_689_, lean_object* v_x_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___f_701_; lean_object* v___x_702_; 
lean_inc(v___y_695_);
lean_inc_ref(v___y_694_);
lean_inc(v___y_693_);
lean_inc_ref(v___y_692_);
lean_inc(v___y_691_);
v___f_701_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_701_, 0, v_x_690_);
lean_closure_set(v___f_701_, 1, v___y_691_);
lean_closure_set(v___f_701_, 2, v___y_692_);
lean_closure_set(v___f_701_, 3, v___y_693_);
lean_closure_set(v___f_701_, 4, v___y_694_);
lean_closure_set(v___f_701_, 5, v___y_695_);
v___x_702_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_689_, v___f_701_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
if (lean_obj_tag(v___x_702_) == 0)
{
return v___x_702_;
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_702_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___boxed(lean_object* v_mvarId_711_, lean_object* v_x_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v_mvarId_711_, v_x_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1(lean_object* v_00_u03b1_724_, lean_object* v_mvarId_725_, lean_object* v_x_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v_mvarId_725_, v_x_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___boxed(lean_object* v_00_u03b1_738_, lean_object* v_mvarId_739_, lean_object* v_x_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1(v_00_u03b1_738_, v_mvarId_739_, v_x_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(lean_object* v_e_752_){
_start:
{
if (lean_obj_tag(v_e_752_) == 0)
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_762_; 
v_a_754_ = lean_ctor_get(v_e_752_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v_e_752_);
if (v_isSharedCheck_762_ == 0)
{
v___x_756_ = v_e_752_;
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v_e_752_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_758_ = lean_mk_io_user_error(v_a_754_);
if (v_isShared_757_ == 0)
{
lean_ctor_set_tag(v___x_756_, 1);
lean_ctor_set(v___x_756_, 0, v___x_758_);
v___x_760_ = v___x_756_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
v_a_763_ = lean_ctor_get(v_e_752_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v_e_752_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v_e_752_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v_e_752_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
lean_ctor_set_tag(v___x_765_, 0);
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg___boxed(lean_object* v_e_771_, lean_object* v_a_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v_e_771_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2(lean_object* v_00_u03b1_774_, lean_object* v_e_775_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v_e_775_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___boxed(lean_object* v_00_u03b1_778_, lean_object* v_e_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2(v_00_u03b1_778_, v_e_779_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(lean_object* v_msg_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_ref_788_; lean_object* v___x_789_; lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_798_; 
v_ref_788_ = lean_ctor_get(v___y_785_, 5);
v___x_789_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v_msg_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
v_a_790_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_798_ == 0)
{
v___x_792_ = v___x_789_;
v_isShared_793_ = v_isSharedCheck_798_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_789_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_798_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_796_; 
lean_inc(v_ref_788_);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v_ref_788_);
lean_ctor_set(v___x_794_, 1, v_a_790_);
if (v_isShared_793_ == 0)
{
lean_ctor_set_tag(v___x_792_, 1);
lean_ctor_set(v___x_792_, 0, v___x_794_);
v___x_796_ = v___x_792_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_794_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg___boxed(lean_object* v_msg_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(v_msg_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(lean_object* v_target_806_, lean_object* v_ctx_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_exprDef_818_; lean_object* v_certDef_819_; lean_object* v_reflectionDef_820_; lean_object* v_solver_821_; lean_object* v_lratPath_822_; lean_object* v_config_823_; lean_object* v_restrictedTypes_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_950_; 
v_exprDef_818_ = lean_ctor_get(v_ctx_807_, 0);
v_certDef_819_ = lean_ctor_get(v_ctx_807_, 1);
v_reflectionDef_820_ = lean_ctor_get(v_ctx_807_, 2);
v_solver_821_ = lean_ctor_get(v_ctx_807_, 3);
v_lratPath_822_ = lean_ctor_get(v_ctx_807_, 4);
v_config_823_ = lean_ctor_get(v_ctx_807_, 5);
v_restrictedTypes_824_ = lean_ctor_get(v_ctx_807_, 6);
v_isSharedCheck_950_ = !lean_is_exclusive(v_ctx_807_);
if (v_isSharedCheck_950_ == 0)
{
v___x_826_ = v_ctx_807_;
v_isShared_827_ = v_isSharedCheck_950_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_restrictedTypes_824_);
lean_inc(v_config_823_);
lean_inc(v_lratPath_822_);
lean_inc(v_solver_821_);
lean_inc(v_reflectionDef_820_);
lean_inc(v_certDef_819_);
lean_inc(v_exprDef_818_);
lean_dec(v_ctx_807_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_950_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v_timeout_850_; uint8_t v_trimProofs_851_; uint8_t v_binaryProofs_852_; uint8_t v_acNf_853_; uint8_t v_andFlattening_854_; uint8_t v_embeddedConstraintSubst_855_; uint8_t v_structures_856_; uint8_t v_fixedInt_857_; uint8_t v_enums_858_; uint8_t v_graphviz_859_; lean_object* v_maxSteps_860_; uint8_t v_shortCircuit_861_; uint8_t v_solverMode_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_949_; 
v_timeout_850_ = lean_ctor_get(v_config_823_, 0);
v_trimProofs_851_ = lean_ctor_get_uint8(v_config_823_, sizeof(void*)*2);
v_binaryProofs_852_ = lean_ctor_get_uint8(v_config_823_, sizeof(void*)*2 + 1);
v_acNf_853_ = lean_ctor_get_uint8(v_config_823_, sizeof(void*)*2 + 2);
v_andFlattening_854_ = lean_ctor_get_uint8(v_config_823_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_855_ = lean_ctor_get_uint8(v_config_823_, sizeof(void*)*2 + 4);
v_structures_856_ = lean_ctor_get_uint8(v_config_823_, sizeof(void*)*2 + 5);
v_fixedInt_857_ = lean_ctor_get_uint8(v_config_823_, sizeof(void*)*2 + 6);
v_enums_858_ = lean_ctor_get_uint8(v_config_823_, sizeof(void*)*2 + 7);
v_graphviz_859_ = lean_ctor_get_uint8(v_config_823_, sizeof(void*)*2 + 8);
v_maxSteps_860_ = lean_ctor_get(v_config_823_, 1);
v_shortCircuit_861_ = lean_ctor_get_uint8(v_config_823_, sizeof(void*)*2 + 9);
v_solverMode_862_ = lean_ctor_get_uint8(v_config_823_, sizeof(void*)*2 + 10);
v_isSharedCheck_949_ = !lean_is_exclusive(v_config_823_);
if (v_isSharedCheck_949_ == 0)
{
v___x_864_ = v_config_823_;
v_isShared_865_ = v_isSharedCheck_949_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_maxSteps_860_);
lean_inc(v_timeout_850_);
lean_dec(v_config_823_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_949_;
goto v_resetjp_863_;
}
v___jp_828_:
{
lean_object* v___x_838_; 
v___x_838_ = l_System_FilePath_fileName(v_lratPath_822_);
if (lean_obj_tag(v___x_838_) == 1)
{
lean_object* v_val_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_847_; 
v_val_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_847_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_val_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_val_839_);
v___x_844_ = v_reuseFailAlloc_846_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_845_; 
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
return v___x_845_;
}
}
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; 
lean_dec(v___x_838_);
v___x_848_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5, &l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5);
v___x_849_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(v___x_848_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
return v___x_849_;
}
}
v_resetjp_863_:
{
lean_object* v___x_866_; uint8_t v___x_867_; lean_object* v___x_869_; 
v___x_866_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_806_);
v___x_867_ = 0;
if (v_isShared_865_ == 0)
{
v___x_869_ = v___x_864_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_timeout_850_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_maxSteps_860_);
lean_ctor_set_uint8(v_reuseFailAlloc_948_, sizeof(void*)*2 + 1, v_binaryProofs_852_);
lean_ctor_set_uint8(v_reuseFailAlloc_948_, sizeof(void*)*2 + 2, v_acNf_853_);
lean_ctor_set_uint8(v_reuseFailAlloc_948_, sizeof(void*)*2 + 3, v_andFlattening_854_);
lean_ctor_set_uint8(v_reuseFailAlloc_948_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_855_);
lean_ctor_set_uint8(v_reuseFailAlloc_948_, sizeof(void*)*2 + 5, v_structures_856_);
lean_ctor_set_uint8(v_reuseFailAlloc_948_, sizeof(void*)*2 + 6, v_fixedInt_857_);
lean_ctor_set_uint8(v_reuseFailAlloc_948_, sizeof(void*)*2 + 7, v_enums_858_);
lean_ctor_set_uint8(v_reuseFailAlloc_948_, sizeof(void*)*2 + 8, v_graphviz_859_);
lean_ctor_set_uint8(v_reuseFailAlloc_948_, sizeof(void*)*2 + 9, v_shortCircuit_861_);
lean_ctor_set_uint8(v_reuseFailAlloc_948_, sizeof(void*)*2 + 10, v_solverMode_862_);
v___x_869_ = v_reuseFailAlloc_948_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_871_; 
lean_ctor_set_uint8(v___x_869_, sizeof(void*)*2, v___x_867_);
lean_inc_ref(v_lratPath_822_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 5, v___x_869_);
v___x_871_ = v___x_826_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_exprDef_818_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_certDef_819_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v_reflectionDef_820_);
lean_ctor_set(v_reuseFailAlloc_947_, 3, v_solver_821_);
lean_ctor_set(v_reuseFailAlloc_947_, 4, v_lratPath_822_);
lean_ctor_set(v_reuseFailAlloc_947_, 5, v___x_869_);
lean_ctor_set(v_reuseFailAlloc_947_, 6, v_restrictedTypes_824_);
v___x_871_ = v_reuseFailAlloc_947_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed), 12, 2);
lean_closure_set(v___x_872_, 0, v_target_806_);
lean_closure_set(v___x_872_, 1, v___x_871_);
v___x_873_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v___x_866_, v___x_872_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_938_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_938_ == 0)
{
v___x_876_ = v___x_873_;
v_isShared_877_ = v_isSharedCheck_938_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_873_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_938_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
if (lean_obj_tag(v_a_874_) == 0)
{
lean_object* v___x_878_; lean_object* v___x_880_; 
lean_dec_ref(v_lratPath_822_);
v___x_878_ = lean_box(0);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_878_);
v___x_880_ = v___x_876_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
else
{
lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_936_; 
lean_del_object(v___x_876_);
v_isSharedCheck_936_ = !lean_is_exclusive(v_a_874_);
if (v_isSharedCheck_936_ == 0)
{
lean_object* v_unused_937_; 
v_unused_937_ = lean_ctor_get(v_a_874_, 0);
lean_dec(v_unused_937_);
v___x_883_ = v_a_874_;
v_isShared_884_ = v_isSharedCheck_936_;
goto v_resetjp_882_;
}
else
{
lean_dec(v_a_874_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_936_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
if (v_trimProofs_851_ == 0)
{
lean_del_object(v___x_883_);
v___y_829_ = v_a_808_;
v___y_830_ = v_a_809_;
v___y_831_ = v_a_810_;
v___y_832_ = v_a_811_;
v___y_833_ = v_a_812_;
v___y_834_ = v_a_813_;
v___y_835_ = v_a_814_;
v___y_836_ = v_a_815_;
v___y_837_ = v_a_816_;
goto v___jp_828_;
}
else
{
lean_object* v___x_885_; 
v___x_885_ = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(v_lratPath_822_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
v___x_887_ = l_Lean_Meta_Tactic_BVDecide_LRAT_trim(v_a_886_);
lean_dec(v_a_886_);
v___x_888_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v___x_887_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_890_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref_known(v___x_888_, 1);
v___x_890_ = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(v_lratPath_822_, v_a_889_, v_binaryProofs_852_);
lean_dec(v_a_889_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_dec_ref_known(v___x_890_, 1);
lean_del_object(v___x_883_);
v___y_829_ = v_a_808_;
v___y_830_ = v_a_809_;
v___y_831_ = v_a_810_;
v___y_832_ = v_a_811_;
v___y_833_ = v_a_812_;
v___y_834_ = v_a_813_;
v___y_835_ = v_a_814_;
v___y_836_ = v_a_815_;
v___y_837_ = v_a_816_;
goto v___jp_828_;
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_905_; 
lean_dec_ref(v_lratPath_822_);
v_a_891_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_905_ == 0)
{
v___x_893_ = v___x_890_;
v_isShared_894_ = v_isSharedCheck_905_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_890_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_905_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v_ref_895_; lean_object* v___x_896_; lean_object* v___x_898_; 
v_ref_895_ = lean_ctor_get(v_a_815_, 5);
v___x_896_ = lean_io_error_to_string(v_a_891_);
if (v_isShared_884_ == 0)
{
lean_ctor_set_tag(v___x_883_, 3);
lean_ctor_set(v___x_883_, 0, v___x_896_);
v___x_898_ = v___x_883_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_896_);
v___x_898_ = v_reuseFailAlloc_904_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_899_ = l_Lean_MessageData_ofFormat(v___x_898_);
lean_inc(v_ref_895_);
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v_ref_895_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v___x_900_);
v___x_902_ = v___x_893_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
else
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_920_; 
lean_dec_ref(v_lratPath_822_);
v_a_906_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_920_ == 0)
{
v___x_908_ = v___x_888_;
v_isShared_909_ = v_isSharedCheck_920_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_888_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_920_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v_ref_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
v_ref_910_ = lean_ctor_get(v_a_815_, 5);
v___x_911_ = lean_io_error_to_string(v_a_906_);
if (v_isShared_884_ == 0)
{
lean_ctor_set_tag(v___x_883_, 3);
lean_ctor_set(v___x_883_, 0, v___x_911_);
v___x_913_ = v___x_883_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_919_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_914_ = l_Lean_MessageData_ofFormat(v___x_913_);
lean_inc(v_ref_910_);
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v_ref_910_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_915_);
v___x_917_ = v___x_908_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_915_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_935_; 
lean_dec_ref(v_lratPath_822_);
v_a_921_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_935_ == 0)
{
v___x_923_ = v___x_885_;
v_isShared_924_ = v_isSharedCheck_935_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_885_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_935_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v_ref_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
v_ref_925_ = lean_ctor_get(v_a_815_, 5);
v___x_926_ = lean_io_error_to_string(v_a_921_);
if (v_isShared_884_ == 0)
{
lean_ctor_set_tag(v___x_883_, 3);
lean_ctor_set(v___x_883_, 0, v___x_926_);
v___x_928_ = v___x_883_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_934_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
v___x_929_ = l_Lean_MessageData_ofFormat(v___x_928_);
lean_inc(v_ref_925_);
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v_ref_925_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_930_);
v___x_932_ = v___x_923_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_930_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
lean_dec_ref(v_lratPath_822_);
v_a_939_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_873_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_873_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___boxed(lean_object* v_target_951_, lean_object* v_ctx_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(v_target_951_, v_ctx_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0(lean_object* v_00_u03b1_964_, lean_object* v_msg_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(v_msg_965_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___boxed(lean_object* v_00_u03b1_977_, lean_object* v_msg_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0(v_00_u03b1_977_, v_msg_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
return v_res_989_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_990_ = lean_box(0);
v___x_991_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v___x_990_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg(){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0);
v___x_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___boxed(lean_object* v___y_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0(lean_object* v_00_u03b1_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___boxed(lean_object* v_00_u03b1_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0(v_00_u03b1_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(lean_object* v_snd_1020_, lean_object* v___y_1021_, lean_object* v_a_x3f_1022_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = lean_io_remove_file(v_snd_1020_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1045_; 
v_a_1033_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1035_ = v___x_1024_;
v_isShared_1036_ = v_isSharedCheck_1045_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1024_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1045_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v_ref_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
v_ref_1037_ = lean_ctor_get(v___y_1021_, 5);
v___x_1038_ = lean_io_error_to_string(v_a_1033_);
v___x_1039_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
v___x_1040_ = l_Lean_MessageData_ofFormat(v___x_1039_);
lean_inc(v_ref_1037_);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v_ref_1037_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1041_);
v___x_1043_ = v___x_1035_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0___boxed(lean_object* v_snd_1046_, lean_object* v___y_1047_, lean_object* v_a_x3f_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_1046_, v___y_1047_, v_a_x3f_1048_);
lean_dec(v_a_x3f_1048_);
lean_dec_ref(v___y_1047_);
lean_dec_ref(v_snd_1046_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(lean_object* v_f_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v_fst_1063_; lean_object* v_snd_1064_; lean_object* v_r_1065_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_a_1062_);
lean_dec_ref_known(v___x_1061_, 1);
v_fst_1063_ = lean_ctor_get(v_a_1062_, 0);
lean_inc(v_fst_1063_);
v_snd_1064_ = lean_ctor_get(v_a_1062_, 1);
lean_inc_n(v_snd_1064_, 2);
lean_dec(v_a_1062_);
lean_inc(v___y_1059_);
lean_inc_ref(v___y_1058_);
lean_inc(v___y_1057_);
lean_inc_ref(v___y_1056_);
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
v_r_1065_ = lean_apply_11(v_f_1051_, v_fst_1063_, v_snd_1064_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, lean_box(0));
if (lean_obj_tag(v_r_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1090_; 
v_a_1066_ = lean_ctor_get(v_r_1065_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_r_1065_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1068_ = v_r_1065_;
v_isShared_1069_ = v_isSharedCheck_1090_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v_r_1065_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1090_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
lean_inc(v_a_1066_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set_tag(v___x_1068_, 1);
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_1064_, v___y_1058_, v___x_1071_);
lean_dec_ref(v___x_1071_);
lean_dec(v_snd_1064_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1079_ == 0)
{
lean_object* v_unused_1080_; 
v_unused_1080_ = lean_ctor_get(v___x_1072_, 0);
lean_dec(v_unused_1080_);
v___x_1074_ = v___x_1072_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_dec(v___x_1072_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v_a_1066_);
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1066_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec(v_a_1066_);
v_a_1081_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1072_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1072_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v_a_1091_ = lean_ctor_get(v_r_1065_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v_r_1065_, 1);
v___x_1092_ = lean_box(0);
v___x_1093_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_1064_, v___y_1058_, v___x_1092_);
lean_dec(v_snd_1064_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; 
v_unused_1101_ = lean_ctor_get(v___x_1093_, 0);
lean_dec(v_unused_1101_);
v___x_1095_ = v___x_1093_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_dec(v___x_1093_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set_tag(v___x_1095_, 1);
lean_ctor_set(v___x_1095_, 0, v_a_1091_);
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1091_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec(v_a_1091_);
v_a_1102_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1093_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1093_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1122_; 
lean_dec_ref(v_f_1051_);
v_a_1110_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1112_ = v___x_1061_;
v_isShared_1113_ = v_isSharedCheck_1122_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1061_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1122_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v_ref_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; 
v_ref_1114_ = lean_ctor_get(v___y_1058_, 5);
v___x_1115_ = lean_io_error_to_string(v_a_1110_);
v___x_1116_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
v___x_1117_ = l_Lean_MessageData_ofFormat(v___x_1116_);
lean_inc(v_ref_1114_);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v_ref_1114_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1118_);
v___x_1120_ = v___x_1112_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___boxed(lean_object* v_f_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(v_f_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1(lean_object* v_00_u03b1_1134_, lean_object* v_f_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(v_f_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___boxed(lean_object* v_00_u03b1_1146_, lean_object* v_f_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1(v_00_u03b1_1146_, v_f_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0(uint8_t v___x_1158_, uint8_t v___x_1159_, lean_object* v___x_1160_, lean_object* v___x_1161_, lean_object* v_a_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1164_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v___x_1172_, 1);
v___x_1174_ = lean_unsigned_to_nat(9u);
v___x_1175_ = lean_unsigned_to_nat(5u);
v___x_1176_ = lean_unsigned_to_nat(8u);
v___x_1177_ = lean_unsigned_to_nat(1000u);
v___x_1178_ = lean_unsigned_to_nat(1024u);
v___x_1179_ = lean_unsigned_to_nat(10000u);
v___x_1180_ = lean_unsigned_to_nat(1048576u);
v___x_1181_ = lean_unsigned_to_nat(50u);
v___x_1182_ = lean_box(0);
v___x_1183_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_1183_, 0, v___x_1174_);
lean_ctor_set(v___x_1183_, 1, v___x_1175_);
lean_ctor_set(v___x_1183_, 2, v___x_1176_);
lean_ctor_set(v___x_1183_, 3, v___x_1176_);
lean_ctor_set(v___x_1183_, 4, v___x_1177_);
lean_ctor_set(v___x_1183_, 5, v___x_1177_);
lean_ctor_set(v___x_1183_, 6, v___x_1160_);
lean_ctor_set(v___x_1183_, 7, v___x_1178_);
lean_ctor_set(v___x_1183_, 8, v___x_1179_);
lean_ctor_set(v___x_1183_, 9, v___x_1177_);
lean_ctor_set(v___x_1183_, 10, v___x_1180_);
lean_ctor_set(v___x_1183_, 11, v___x_1161_);
lean_ctor_set(v___x_1183_, 12, v___x_1181_);
lean_ctor_set(v___x_1183_, 13, v___x_1182_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14, v___x_1158_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 1, v___x_1158_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 2, v___x_1158_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 3, v___x_1158_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 4, v___x_1158_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 5, v___x_1159_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 6, v___x_1159_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 7, v___x_1159_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 8, v___x_1158_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 9, v___x_1158_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 10, v___x_1159_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 11, v___x_1158_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 12, v___x_1159_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 13, v___x_1159_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 14, v___x_1159_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 15, v___x_1159_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 16, v___x_1159_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 17, v___x_1158_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 18, v___x_1159_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 19, v___x_1159_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 20, v___x_1159_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 21, v___x_1159_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 22, v___x_1159_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 23, v___x_1159_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 24, v___x_1159_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 25, v___x_1159_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 26, v___x_1159_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 27, v___x_1159_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 28, v___x_1159_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 29, v___x_1159_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 30, v___x_1158_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 31, v___x_1159_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*14 + 32, v___x_1159_);
v___x_1184_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_1183_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_a_1185_);
lean_dec_ref_known(v___x_1184_, 1);
v___x_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1186_, 0, v_a_1173_);
v___x_1187_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed), 12, 2);
lean_closure_set(v___x_1187_, 0, v___x_1186_);
lean_closure_set(v___x_1187_, 1, v_a_1162_);
v___x_1188_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___x_1187_, v_a_1185_, v___x_1182_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
lean_dec_ref_known(v___x_1188_, 1);
v___x_1189_ = lean_box(0);
v___x_1190_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1189_, v___y_1164_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1198_; 
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; 
v_unused_1199_ = lean_ctor_get(v___x_1190_, 0);
lean_dec(v_unused_1199_);
v___x_1192_ = v___x_1190_;
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
else
{
lean_dec(v___x_1190_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1194_ = lean_box(0);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1194_);
v___x_1196_ = v___x_1192_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
else
{
return v___x_1190_;
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
v_a_1200_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1188_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1188_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_dec(v_a_1173_);
lean_dec_ref(v_a_1162_);
v_a_1208_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1184_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1184_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec_ref(v_a_1162_);
lean_dec(v___x_1161_);
lean_dec(v___x_1160_);
v_a_1216_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1172_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1172_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0___boxed(lean_object* v___x_1224_, lean_object* v___x_1225_, lean_object* v___x_1226_, lean_object* v___x_1227_, lean_object* v_a_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
uint8_t v___x_6747__boxed_1238_; uint8_t v___x_6748__boxed_1239_; lean_object* v_res_1240_; 
v___x_6747__boxed_1238_ = lean_unbox(v___x_1224_);
v___x_6748__boxed_1239_ = lean_unbox(v___x_1225_);
v_res_1240_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0(v___x_6747__boxed_1238_, v___x_6748__boxed_1239_, v___x_1226_, v___x_1227_, v_a_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1(lean_object* v_a_1241_, lean_object* v_a_1242_, uint8_t v___x_1243_, uint8_t v___x_1244_, lean_object* v___x_1245_, lean_object* v___x_1246_, lean_object* v_x_1247_, lean_object* v_lratFile_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new(v_lratFile_1248_, v_a_1241_, v_a_1242_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___f_1262_; lean_object* v___x_1263_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref_known(v___x_1258_, 1);
v___x_1260_ = lean_box(v___x_1243_);
v___x_1261_ = lean_box(v___x_1244_);
v___f_1262_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0___boxed), 14, 5);
lean_closure_set(v___f_1262_, 0, v___x_1260_);
lean_closure_set(v___f_1262_, 1, v___x_1261_);
lean_closure_set(v___f_1262_, 2, v___x_1245_);
lean_closure_set(v___f_1262_, 3, v___x_1246_);
lean_closure_set(v___f_1262_, 4, v_a_1259_);
v___x_1263_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1262_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
return v___x_1263_;
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v___x_1246_);
lean_dec(v___x_1245_);
v_a_1264_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1258_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1258_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1___boxed(lean_object** _args){
lean_object* v_a_1272_ = _args[0];
lean_object* v_a_1273_ = _args[1];
lean_object* v___x_1274_ = _args[2];
lean_object* v___x_1275_ = _args[3];
lean_object* v___x_1276_ = _args[4];
lean_object* v___x_1277_ = _args[5];
lean_object* v_x_1278_ = _args[6];
lean_object* v_lratFile_1279_ = _args[7];
lean_object* v___y_1280_ = _args[8];
lean_object* v___y_1281_ = _args[9];
lean_object* v___y_1282_ = _args[10];
lean_object* v___y_1283_ = _args[11];
lean_object* v___y_1284_ = _args[12];
lean_object* v___y_1285_ = _args[13];
lean_object* v___y_1286_ = _args[14];
lean_object* v___y_1287_ = _args[15];
lean_object* v___y_1288_ = _args[16];
_start:
{
uint8_t v___x_6898__boxed_1289_; uint8_t v___x_6899__boxed_1290_; lean_object* v_res_1291_; 
v___x_6898__boxed_1289_ = lean_unbox(v___x_1274_);
v___x_6899__boxed_1290_ = lean_unbox(v___x_1275_);
v_res_1291_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1(v_a_1272_, v_a_1273_, v___x_6898__boxed_1289_, v___x_6899__boxed_1290_, v___x_1276_, v___x_1277_, v_x_1278_, v_lratFile_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v_x_1278_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide(lean_object* v_x_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1322_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3));
lean_inc(v_x_1312_);
v___x_1323_ = l_Lean_Syntax_isOfKind(v_x_1312_, v___x_1322_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; 
lean_dec(v_x_1312_);
v___x_1324_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1324_;
}
else
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; lean_object* v_types_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; 
v___x_1325_ = lean_unsigned_to_nat(1u);
v___x_1326_ = l_Lean_Syntax_getArg(v_x_1312_, v___x_1325_);
v___x_1327_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_1326_);
v___x_1328_ = l_Lean_Syntax_isOfKind(v___x_1326_, v___x_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1369_; 
lean_dec(v___x_1326_);
lean_dec(v_x_1312_);
v___x_1369_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1369_;
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v___x_1370_ = lean_unsigned_to_nat(2u);
v___x_1371_ = l_Lean_Syntax_getArg(v_x_1312_, v___x_1370_);
lean_dec(v_x_1312_);
v___x_1372_ = l_Lean_Syntax_isNone(v___x_1371_);
if (v___x_1372_ == 0)
{
uint8_t v___x_1373_; 
lean_inc(v___x_1371_);
v___x_1373_ = l_Lean_Syntax_matchesNull(v___x_1371_, v___x_1325_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; 
lean_dec(v___x_1371_);
lean_dec(v___x_1326_);
v___x_1374_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1374_;
}
else
{
lean_object* v___x_1375_; lean_object* v_types_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1375_ = lean_unsigned_to_nat(0u);
v_types_1376_ = l_Lean_Syntax_getArg(v___x_1371_, v___x_1375_);
lean_dec(v___x_1371_);
v___x_1377_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_types_1376_);
v___x_1378_ = l_Lean_Syntax_isOfKind(v_types_1376_, v___x_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; 
lean_dec(v_types_1376_);
lean_dec(v___x_1326_);
v___x_1379_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1379_;
}
else
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1380_, 0, v_types_1376_);
v_types_1330_ = v___x_1380_;
v___y_1331_ = v_a_1313_;
v___y_1332_ = v_a_1314_;
v___y_1333_ = v_a_1315_;
v___y_1334_ = v_a_1316_;
v___y_1335_ = v_a_1317_;
v___y_1336_ = v_a_1318_;
v___y_1337_ = v_a_1319_;
v___y_1338_ = v_a_1320_;
goto v___jp_1329_;
}
}
}
else
{
lean_object* v___x_1381_; 
lean_dec(v___x_1371_);
v___x_1381_ = lean_box(0);
v_types_1330_ = v___x_1381_;
v___y_1331_ = v_a_1313_;
v___y_1332_ = v_a_1314_;
v___y_1333_ = v_a_1315_;
v___y_1334_ = v_a_1316_;
v___y_1335_ = v_a_1317_;
v___y_1336_ = v_a_1318_;
v___y_1337_ = v_a_1319_;
v___y_1338_ = v_a_1320_;
goto v___jp_1329_;
}
}
v___jp_1329_:
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1337_, v___y_1338_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v___x_1340_; uint8_t v___x_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
lean_dec_ref_known(v___x_1339_, 1);
v___x_1340_ = lean_unsigned_to_nat(10u);
v___x_1341_ = 0;
v___x_1342_ = lean_unsigned_to_nat(100000u);
v___x_1343_ = 0;
v___x_1344_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_1344_, 0, v___x_1340_);
lean_ctor_set(v___x_1344_, 1, v___x_1342_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*2, v___x_1328_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*2 + 1, v___x_1328_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*2 + 2, v___x_1341_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*2 + 3, v___x_1328_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*2 + 4, v___x_1328_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*2 + 5, v___x_1328_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*2 + 6, v___x_1328_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*2 + 7, v___x_1328_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*2 + 8, v___x_1341_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*2 + 9, v___x_1341_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*2 + 10, v___x_1343_);
v___x_1345_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_1326_, v___x_1344_, v___x_1328_, v___y_1331_, v___y_1337_, v___y_1338_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1347_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1345_, 1);
v___x_1347_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_types_1330_, v_a_1346_, v___y_1337_, v___y_1338_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___f_1351_; lean_object* v___x_1352_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1347_, 1);
v___x_1349_ = lean_box(v___x_1341_);
v___x_1350_ = lean_box(v___x_1328_);
v___f_1351_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1___boxed), 17, 6);
lean_closure_set(v___f_1351_, 0, v_a_1346_);
lean_closure_set(v___f_1351_, 1, v_a_1348_);
lean_closure_set(v___f_1351_, 2, v___x_1349_);
lean_closure_set(v___f_1351_, 3, v___x_1350_);
lean_closure_set(v___f_1351_, 4, v___x_1342_);
lean_closure_set(v___f_1351_, 5, v___x_1340_);
v___x_1352_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(v___f_1351_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
return v___x_1352_;
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_dec(v_a_1346_);
v_a_1353_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1347_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1347_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec(v_types_1330_);
v_a_1361_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1345_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1345_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
else
{
lean_dec(v_types_1330_);
lean_dec(v___x_1326_);
return v___x_1339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___boxed(lean_object* v_x_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide(v_x_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_);
lean_dec(v_a_1390_);
lean_dec_ref(v_a_1389_);
lean_dec(v_a_1388_);
lean_dec_ref(v_a_1387_);
lean_dec(v_a_1386_);
lean_dec_ref(v_a_1385_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1(){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1402_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1403_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3));
v___x_1404_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2));
v___x_1405_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___boxed), 10, 0);
v___x_1406_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1402_, v___x_1403_, v___x_1404_, v___x_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___boxed(lean_object* v_a_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1();
return v_res_1408_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_Array_mkArray0(lean_box(0));
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0(lean_object* v___x_1421_, lean_object* v_a_1422_, uint8_t v___x_1423_, lean_object* v___x_1424_, lean_object* v___x_1425_, lean_object* v___x_1426_, lean_object* v___x_1427_, lean_object* v_tk_1428_, lean_object* v_typesStx_1429_, lean_object* v___x_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(v___x_1421_, v_a_1422_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_a_1442_);
lean_dec_ref_known(v___x_1441_, 1);
if (lean_obj_tag(v_a_1442_) == 0)
{
lean_object* v_ref_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___y_1453_; 
v_ref_1443_ = lean_ctor_get(v___y_1438_, 5);
v___x_1444_ = l_Lean_SourceInfo_fromRef(v_ref_1443_, v___x_1423_);
v___x_1445_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__1));
v___x_1446_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__2));
v___x_1447_ = l_Lean_Name_mkStr4(v___x_1424_, v___x_1425_, v___x_1426_, v___x_1446_);
v___x_1448_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3));
lean_inc(v___x_1444_);
v___x_1449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1444_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5));
v___x_1451_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6);
if (lean_obj_tag(v_typesStx_1429_) == 1)
{
lean_object* v_val_1465_; lean_object* v___x_1466_; 
v_val_1465_ = lean_ctor_get(v_typesStx_1429_, 0);
lean_inc(v_val_1465_);
lean_dec_ref_known(v_typesStx_1429_, 1);
v___x_1466_ = l_Array_mkArray1___redArg(v_val_1465_);
v___y_1453_ = v___x_1466_;
goto v___jp_1452_;
}
else
{
lean_object* v___x_1467_; 
lean_dec(v_typesStx_1429_);
v___x_1467_ = lean_mk_empty_array_with_capacity(v___x_1430_);
v___y_1453_ = v___x_1467_;
goto v___jp_1452_;
}
v___jp_1452_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1454_ = l_Array_append___redArg(v___x_1451_, v___y_1453_);
lean_dec_ref(v___y_1453_);
lean_inc(v___x_1444_);
v___x_1455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1444_);
lean_ctor_set(v___x_1455_, 1, v___x_1450_);
lean_ctor_set(v___x_1455_, 2, v___x_1454_);
v___x_1456_ = l_Lean_Syntax_node3(v___x_1444_, v___x_1447_, v___x_1449_, v___x_1427_, v___x_1455_);
v___x_1457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1445_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v___x_1458_ = lean_box(0);
v___x_1459_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1457_);
lean_ctor_set(v___x_1459_, 1, v___x_1458_);
lean_ctor_set(v___x_1459_, 2, v___x_1458_);
lean_ctor_set(v___x_1459_, 3, v___x_1458_);
lean_ctor_set(v___x_1459_, 4, v___x_1458_);
lean_ctor_set(v___x_1459_, 5, v___x_1458_);
lean_inc(v_ref_1443_);
v___x_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1460_, 0, v_ref_1443_);
v___x_1461_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__7));
v___x_1462_ = 4;
v___x_1463_ = l_Lean_MessageData_nil;
v___x_1464_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1428_, v___x_1459_, v___x_1460_, v___x_1461_, v___x_1458_, v___x_1462_, v___x_1463_, v___y_1438_, v___y_1439_);
return v___x_1464_;
}
}
else
{
lean_object* v_path_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1501_; 
v_path_1468_ = lean_ctor_get(v_a_1442_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_a_1442_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1470_ = v_a_1442_;
v_isShared_1471_ = v_isSharedCheck_1501_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_path_1468_);
lean_dec(v_a_1442_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1501_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v_ref_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___y_1482_; 
v_ref_1472_ = lean_ctor_get(v___y_1438_, 5);
v___x_1473_ = l_Lean_SourceInfo_fromRef(v_ref_1472_, v___x_1423_);
v___x_1474_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__1));
v___x_1475_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__8));
v___x_1476_ = l_Lean_Name_mkStr4(v___x_1424_, v___x_1425_, v___x_1426_, v___x_1475_);
v___x_1477_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__9));
lean_inc(v___x_1473_);
v___x_1478_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1473_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5));
v___x_1480_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6);
if (lean_obj_tag(v_typesStx_1429_) == 1)
{
lean_object* v_val_1498_; lean_object* v___x_1499_; 
v_val_1498_ = lean_ctor_get(v_typesStx_1429_, 0);
lean_inc(v_val_1498_);
lean_dec_ref_known(v_typesStx_1429_, 1);
v___x_1499_ = l_Array_mkArray1___redArg(v_val_1498_);
v___y_1482_ = v___x_1499_;
goto v___jp_1481_;
}
else
{
lean_object* v___x_1500_; 
lean_dec(v_typesStx_1429_);
v___x_1500_ = lean_mk_empty_array_with_capacity(v___x_1430_);
v___y_1482_ = v___x_1500_;
goto v___jp_1481_;
}
v___jp_1481_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1483_ = l_Array_append___redArg(v___x_1480_, v___y_1482_);
lean_dec_ref(v___y_1482_);
lean_inc(v___x_1473_);
v___x_1484_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1473_);
lean_ctor_set(v___x_1484_, 1, v___x_1479_);
lean_ctor_set(v___x_1484_, 2, v___x_1483_);
v___x_1485_ = lean_box(2);
v___x_1486_ = l_Lean_Syntax_mkStrLit(v_path_1468_, v___x_1485_);
v___x_1487_ = l_Lean_Syntax_node4(v___x_1473_, v___x_1476_, v___x_1478_, v___x_1427_, v___x_1484_, v___x_1486_);
v___x_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1474_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = lean_box(0);
v___x_1490_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1488_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
lean_ctor_set(v___x_1490_, 2, v___x_1489_);
lean_ctor_set(v___x_1490_, 3, v___x_1489_);
lean_ctor_set(v___x_1490_, 4, v___x_1489_);
lean_ctor_set(v___x_1490_, 5, v___x_1489_);
lean_inc(v_ref_1472_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 0, v_ref_1472_);
v___x_1492_ = v___x_1470_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_ref_1472_);
v___x_1492_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v___x_1493_; uint8_t v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1493_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__7));
v___x_1494_ = 4;
v___x_1495_ = l_Lean_MessageData_nil;
v___x_1496_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1428_, v___x_1490_, v___x_1492_, v___x_1493_, v___x_1489_, v___x_1494_, v___x_1495_, v___y_1438_, v___y_1439_);
return v___x_1496_;
}
}
}
}
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
lean_dec(v_typesStx_1429_);
lean_dec(v_tk_1428_);
lean_dec(v___x_1427_);
lean_dec_ref(v___x_1426_);
lean_dec_ref(v___x_1425_);
lean_dec_ref(v___x_1424_);
v_a_1502_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1441_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1441_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___boxed(lean_object** _args){
lean_object* v___x_1510_ = _args[0];
lean_object* v_a_1511_ = _args[1];
lean_object* v___x_1512_ = _args[2];
lean_object* v___x_1513_ = _args[3];
lean_object* v___x_1514_ = _args[4];
lean_object* v___x_1515_ = _args[5];
lean_object* v___x_1516_ = _args[6];
lean_object* v_tk_1517_ = _args[7];
lean_object* v_typesStx_1518_ = _args[8];
lean_object* v___x_1519_ = _args[9];
lean_object* v___y_1520_ = _args[10];
lean_object* v___y_1521_ = _args[11];
lean_object* v___y_1522_ = _args[12];
lean_object* v___y_1523_ = _args[13];
lean_object* v___y_1524_ = _args[14];
lean_object* v___y_1525_ = _args[15];
lean_object* v___y_1526_ = _args[16];
lean_object* v___y_1527_ = _args[17];
lean_object* v___y_1528_ = _args[18];
lean_object* v___y_1529_ = _args[19];
_start:
{
uint8_t v___x_22051__boxed_1530_; lean_object* v_res_1531_; 
v___x_22051__boxed_1530_ = lean_unbox(v___x_1512_);
v_res_1531_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0(v___x_1510_, v_a_1511_, v___x_22051__boxed_1530_, v___x_1513_, v___x_1514_, v___x_1515_, v___x_1516_, v_tk_1517_, v_typesStx_1518_, v___x_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec(v___x_1519_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic(lean_object* v_x_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
v___x_1548_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0));
v___x_1549_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1));
v___x_1550_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1));
v___x_1551_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__1));
lean_inc(v_x_1538_);
v___x_1552_ = l_Lean_Syntax_isOfKind(v_x_1538_, v___x_1551_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; 
lean_dec(v_x_1538_);
v___x_1553_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1553_;
}
else
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1554_ = lean_unsigned_to_nat(1u);
v___x_1555_ = l_Lean_Syntax_getArg(v_x_1538_, v___x_1554_);
v___x_1556_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_1555_);
v___x_1557_ = l_Lean_Syntax_isOfKind(v___x_1555_, v___x_1556_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; 
lean_dec(v___x_1555_);
lean_dec(v_x_1538_);
v___x_1558_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1558_;
}
else
{
lean_object* v___x_1559_; lean_object* v_tk_1560_; lean_object* v_typesStx_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___x_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; 
v___x_1559_ = lean_unsigned_to_nat(0u);
v_tk_1560_ = l_Lean_Syntax_getArg(v_x_1538_, v___x_1559_);
v___x_1648_ = lean_unsigned_to_nat(2u);
v___x_1649_ = l_Lean_Syntax_getArg(v_x_1538_, v___x_1648_);
lean_dec(v_x_1538_);
v___x_1650_ = l_Lean_Syntax_isNone(v___x_1649_);
if (v___x_1650_ == 0)
{
uint8_t v___x_1651_; 
lean_inc(v___x_1649_);
v___x_1651_ = l_Lean_Syntax_matchesNull(v___x_1649_, v___x_1554_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; 
lean_dec(v___x_1649_);
lean_dec(v_tk_1560_);
lean_dec(v___x_1555_);
v___x_1652_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1652_;
}
else
{
lean_object* v_typesStx_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; 
v_typesStx_1653_ = l_Lean_Syntax_getArg(v___x_1649_, v___x_1559_);
lean_dec(v___x_1649_);
v___x_1654_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_typesStx_1653_);
v___x_1655_ = l_Lean_Syntax_isOfKind(v_typesStx_1653_, v___x_1654_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; 
lean_dec(v_typesStx_1653_);
lean_dec(v_tk_1560_);
lean_dec(v___x_1555_);
v___x_1656_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1656_;
}
else
{
lean_object* v___x_1657_; 
v___x_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1657_, 0, v_typesStx_1653_);
v_typesStx_1562_ = v___x_1657_;
v___y_1563_ = v_a_1539_;
v___y_1564_ = v_a_1540_;
v___y_1565_ = v_a_1541_;
v___y_1566_ = v_a_1542_;
v___y_1567_ = v_a_1543_;
v___y_1568_ = v_a_1544_;
v___y_1569_ = v_a_1545_;
v___y_1570_ = v_a_1546_;
goto v___jp_1561_;
}
}
}
else
{
lean_object* v___x_1658_; 
lean_dec(v___x_1649_);
v___x_1658_ = lean_box(0);
v_typesStx_1562_ = v___x_1658_;
v___y_1563_ = v_a_1539_;
v___y_1564_ = v_a_1540_;
v___y_1565_ = v_a_1541_;
v___y_1566_ = v_a_1542_;
v___y_1567_ = v_a_1543_;
v___y_1568_ = v_a_1544_;
v___y_1569_ = v_a_1545_;
v___y_1570_ = v_a_1546_;
goto v___jp_1561_;
}
v___jp_1561_:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1646_; 
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1646_ == 0)
{
lean_object* v_unused_1647_; 
v_unused_1647_ = lean_ctor_get(v___x_1571_, 0);
lean_dec(v_unused_1647_);
v___x_1573_ = v___x_1571_;
v_isShared_1574_ = v_isSharedCheck_1646_;
goto v_resetjp_1572_;
}
else
{
lean_dec(v___x_1571_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1646_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; uint8_t v___x_1576_; lean_object* v___x_1577_; uint8_t v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1575_ = lean_unsigned_to_nat(10u);
v___x_1576_ = 0;
v___x_1577_ = lean_unsigned_to_nat(100000u);
v___x_1578_ = 0;
v___x_1579_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_1579_, 0, v___x_1575_);
lean_ctor_set(v___x_1579_, 1, v___x_1577_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*2, v___x_1557_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*2 + 1, v___x_1557_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*2 + 2, v___x_1576_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*2 + 3, v___x_1557_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*2 + 4, v___x_1557_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*2 + 5, v___x_1557_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*2 + 6, v___x_1557_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*2 + 7, v___x_1557_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*2 + 8, v___x_1576_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*2 + 9, v___x_1576_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*2 + 10, v___x_1578_);
lean_inc(v___x_1555_);
v___x_1580_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_1555_, v___x_1579_, v___x_1557_, v___y_1563_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1582_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v___x_1580_, 1);
lean_inc(v_typesStx_1562_);
v___x_1582_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_1562_, v_a_1581_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v___x_1584_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(v_a_1581_, v_a_1583_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1586_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1586_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1564_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1586_, 1);
v___x_1588_ = lean_unsigned_to_nat(9u);
v___x_1589_ = lean_unsigned_to_nat(5u);
v___x_1590_ = lean_unsigned_to_nat(8u);
v___x_1591_ = lean_unsigned_to_nat(1000u);
v___x_1592_ = lean_unsigned_to_nat(1024u);
v___x_1593_ = lean_unsigned_to_nat(10000u);
v___x_1594_ = lean_unsigned_to_nat(1048576u);
v___x_1595_ = lean_unsigned_to_nat(50u);
v___x_1596_ = lean_box(0);
v___x_1597_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_1597_, 0, v___x_1588_);
lean_ctor_set(v___x_1597_, 1, v___x_1589_);
lean_ctor_set(v___x_1597_, 2, v___x_1590_);
lean_ctor_set(v___x_1597_, 3, v___x_1590_);
lean_ctor_set(v___x_1597_, 4, v___x_1591_);
lean_ctor_set(v___x_1597_, 5, v___x_1591_);
lean_ctor_set(v___x_1597_, 6, v___x_1577_);
lean_ctor_set(v___x_1597_, 7, v___x_1592_);
lean_ctor_set(v___x_1597_, 8, v___x_1593_);
lean_ctor_set(v___x_1597_, 9, v___x_1591_);
lean_ctor_set(v___x_1597_, 10, v___x_1594_);
lean_ctor_set(v___x_1597_, 11, v___x_1575_);
lean_ctor_set(v___x_1597_, 12, v___x_1595_);
lean_ctor_set(v___x_1597_, 13, v___x_1596_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14, v___x_1576_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 1, v___x_1576_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 2, v___x_1576_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 3, v___x_1576_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 4, v___x_1576_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 5, v___x_1557_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 6, v___x_1557_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 7, v___x_1557_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 8, v___x_1576_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 9, v___x_1576_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 10, v___x_1557_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 11, v___x_1576_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 12, v___x_1557_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 13, v___x_1557_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 14, v___x_1557_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 15, v___x_1557_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 16, v___x_1557_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 17, v___x_1576_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 18, v___x_1557_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 19, v___x_1557_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 20, v___x_1557_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 21, v___x_1557_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 22, v___x_1557_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 23, v___x_1557_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 24, v___x_1557_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 25, v___x_1557_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 26, v___x_1557_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 27, v___x_1557_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 28, v___x_1557_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 29, v___x_1557_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 30, v___x_1576_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 31, v___x_1557_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 32, v___x_1557_);
v___x_1598_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_1597_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1601_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v_a_1587_);
v___x_1601_ = v___x_1573_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1587_);
v___x_1601_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
lean_object* v___x_1602_; lean_object* v___f_1603_; lean_object* v___x_1604_; 
v___x_1602_ = lean_box(v___x_1576_);
v___f_1603_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___boxed), 20, 10);
lean_closure_set(v___f_1603_, 0, v___x_1601_);
lean_closure_set(v___f_1603_, 1, v_a_1585_);
lean_closure_set(v___f_1603_, 2, v___x_1602_);
lean_closure_set(v___f_1603_, 3, v___x_1548_);
lean_closure_set(v___f_1603_, 4, v___x_1549_);
lean_closure_set(v___f_1603_, 5, v___x_1550_);
lean_closure_set(v___f_1603_, 6, v___x_1555_);
lean_closure_set(v___f_1603_, 7, v_tk_1560_);
lean_closure_set(v___f_1603_, 8, v_typesStx_1562_);
lean_closure_set(v___f_1603_, 9, v___x_1559_);
v___x_1604_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___f_1603_, v_a_1599_, v___x_1596_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
return v___x_1604_;
}
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_dec(v_a_1587_);
lean_dec(v_a_1585_);
lean_del_object(v___x_1573_);
lean_dec(v_typesStx_1562_);
lean_dec(v_tk_1560_);
lean_dec(v___x_1555_);
v_a_1606_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1598_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1598_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_dec(v_a_1585_);
lean_del_object(v___x_1573_);
lean_dec(v_typesStx_1562_);
lean_dec(v_tk_1560_);
lean_dec(v___x_1555_);
v_a_1614_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1586_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1586_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_del_object(v___x_1573_);
lean_dec(v_typesStx_1562_);
lean_dec(v_tk_1560_);
lean_dec(v___x_1555_);
v_a_1622_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1584_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1584_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec(v_a_1581_);
lean_del_object(v___x_1573_);
lean_dec(v_typesStx_1562_);
lean_dec(v_tk_1560_);
lean_dec(v___x_1555_);
v_a_1630_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1582_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1582_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_del_object(v___x_1573_);
lean_dec(v_typesStx_1562_);
lean_dec(v_tk_1560_);
lean_dec(v___x_1555_);
v_a_1638_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1580_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1580_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
else
{
lean_dec(v_typesStx_1562_);
lean_dec(v_tk_1560_);
lean_dec(v___x_1555_);
return v___x_1571_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___boxed(lean_object* v_x_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic(v_x_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
lean_dec(v_a_1667_);
lean_dec_ref(v_a_1666_);
lean_dec(v_a_1665_);
lean_dec_ref(v_a_1664_);
lean_dec(v_a_1663_);
lean_dec_ref(v_a_1662_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1(){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1678_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1679_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__1));
v___x_1680_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___closed__1));
v___x_1681_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___boxed), 10, 0);
v___x_1682_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1678_, v___x_1679_, v___x_1680_, v___x_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___boxed(lean_object* v_a_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1();
return v_res_1684_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_1691_, uint8_t v_suppressElabErrors_1692_, lean_object* v_x_1693_){
_start:
{
if (lean_obj_tag(v_x_1693_) == 1)
{
lean_object* v_pre_1694_; 
v_pre_1694_ = lean_ctor_get(v_x_1693_, 0);
switch(lean_obj_tag(v_pre_1694_))
{
case 1:
{
lean_object* v_pre_1695_; 
v_pre_1695_ = lean_ctor_get(v_pre_1694_, 0);
switch(lean_obj_tag(v_pre_1695_))
{
case 0:
{
lean_object* v_str_1696_; lean_object* v_str_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; 
v_str_1696_ = lean_ctor_get(v_x_1693_, 1);
v_str_1697_ = lean_ctor_get(v_pre_1694_, 1);
v___x_1698_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__0));
v___x_1699_ = lean_string_dec_eq(v_str_1697_, v___x_1698_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; uint8_t v___x_1701_; 
v___x_1700_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1));
v___x_1701_ = lean_string_dec_eq(v_str_1697_, v___x_1700_);
if (v___x_1701_ == 0)
{
return v___y_1691_;
}
else
{
lean_object* v___x_1702_; uint8_t v___x_1703_; 
v___x_1702_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_1703_ = lean_string_dec_eq(v_str_1696_, v___x_1702_);
if (v___x_1703_ == 0)
{
return v___y_1691_;
}
else
{
return v_suppressElabErrors_1692_;
}
}
}
else
{
lean_object* v___x_1704_; uint8_t v___x_1705_; 
v___x_1704_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_1705_ = lean_string_dec_eq(v_str_1696_, v___x_1704_);
if (v___x_1705_ == 0)
{
return v___y_1691_;
}
else
{
return v_suppressElabErrors_1692_;
}
}
}
case 1:
{
lean_object* v_pre_1706_; 
v_pre_1706_ = lean_ctor_get(v_pre_1695_, 0);
if (lean_obj_tag(v_pre_1706_) == 0)
{
lean_object* v_str_1707_; lean_object* v_str_1708_; lean_object* v_str_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; 
v_str_1707_ = lean_ctor_get(v_x_1693_, 1);
v_str_1708_ = lean_ctor_get(v_pre_1694_, 1);
v_str_1709_ = lean_ctor_get(v_pre_1695_, 1);
v___x_1710_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_1711_ = lean_string_dec_eq(v_str_1709_, v___x_1710_);
if (v___x_1711_ == 0)
{
return v___y_1691_;
}
else
{
lean_object* v___x_1712_; uint8_t v___x_1713_; 
v___x_1712_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_1713_ = lean_string_dec_eq(v_str_1708_, v___x_1712_);
if (v___x_1713_ == 0)
{
return v___y_1691_;
}
else
{
lean_object* v___x_1714_; uint8_t v___x_1715_; 
v___x_1714_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_1715_ = lean_string_dec_eq(v_str_1707_, v___x_1714_);
if (v___x_1715_ == 0)
{
return v___y_1691_;
}
else
{
return v_suppressElabErrors_1692_;
}
}
}
}
else
{
return v___y_1691_;
}
}
default: 
{
return v___y_1691_;
}
}
}
case 0:
{
lean_object* v_str_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; 
v_str_1716_ = lean_ctor_get(v_x_1693_, 1);
v___x_1717_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_1718_ = lean_string_dec_eq(v_str_1716_, v___x_1717_);
if (v___x_1718_ == 0)
{
return v___y_1691_;
}
else
{
return v_suppressElabErrors_1692_;
}
}
default: 
{
return v___y_1691_;
}
}
}
else
{
return v___y_1691_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_1719_, lean_object* v_suppressElabErrors_1720_, lean_object* v_x_1721_){
_start:
{
uint8_t v___y_8349__boxed_1722_; uint8_t v_suppressElabErrors_boxed_1723_; uint8_t v_res_1724_; lean_object* v_r_1725_; 
v___y_8349__boxed_1722_ = lean_unbox(v___y_1719_);
v_suppressElabErrors_boxed_1723_ = lean_unbox(v_suppressElabErrors_1720_);
v_res_1724_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0(v___y_8349__boxed_1722_, v_suppressElabErrors_boxed_1723_, v_x_1721_);
lean_dec(v_x_1721_);
v_r_1725_ = lean_box(v_res_1724_);
return v_r_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(lean_object* v_ref_1727_, lean_object* v_msgData_1728_, uint8_t v_severity_1729_, uint8_t v_isSilent_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v___y_1737_; uint8_t v___y_1738_; uint8_t v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; uint8_t v___y_1776_; uint8_t v___y_1777_; uint8_t v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; uint8_t v___y_1801_; uint8_t v___y_1802_; uint8_t v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; uint8_t v___y_1812_; uint8_t v___y_1813_; lean_object* v___y_1814_; uint8_t v___y_1815_; uint8_t v___x_1820_; lean_object* v___y_1822_; lean_object* v___y_1823_; uint8_t v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; uint8_t v___y_1827_; uint8_t v___y_1828_; uint8_t v___y_1830_; uint8_t v___x_1845_; 
v___x_1820_ = 2;
v___x_1845_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1729_, v___x_1820_);
if (v___x_1845_ == 0)
{
v___y_1830_ = v___x_1845_;
goto v___jp_1829_;
}
else
{
uint8_t v___x_1846_; 
lean_inc_ref(v_msgData_1728_);
v___x_1846_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1728_);
v___y_1830_ = v___x_1846_;
goto v___jp_1829_;
}
v___jp_1736_:
{
lean_object* v___x_1746_; lean_object* v_currNamespace_1747_; lean_object* v_openDecls_1748_; lean_object* v_env_1749_; lean_object* v_nextMacroScope_1750_; lean_object* v_ngen_1751_; lean_object* v_auxDeclNGen_1752_; lean_object* v_traceState_1753_; lean_object* v_cache_1754_; lean_object* v_messages_1755_; lean_object* v_infoState_1756_; lean_object* v_snapshotTasks_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1771_; 
v___x_1746_ = lean_st_ref_take(v___y_1745_);
v_currNamespace_1747_ = lean_ctor_get(v___y_1744_, 6);
v_openDecls_1748_ = lean_ctor_get(v___y_1744_, 7);
v_env_1749_ = lean_ctor_get(v___x_1746_, 0);
v_nextMacroScope_1750_ = lean_ctor_get(v___x_1746_, 1);
v_ngen_1751_ = lean_ctor_get(v___x_1746_, 2);
v_auxDeclNGen_1752_ = lean_ctor_get(v___x_1746_, 3);
v_traceState_1753_ = lean_ctor_get(v___x_1746_, 4);
v_cache_1754_ = lean_ctor_get(v___x_1746_, 5);
v_messages_1755_ = lean_ctor_get(v___x_1746_, 6);
v_infoState_1756_ = lean_ctor_get(v___x_1746_, 7);
v_snapshotTasks_1757_ = lean_ctor_get(v___x_1746_, 8);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1759_ = v___x_1746_;
v_isShared_1760_ = v_isSharedCheck_1771_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_snapshotTasks_1757_);
lean_inc(v_infoState_1756_);
lean_inc(v_messages_1755_);
lean_inc(v_cache_1754_);
lean_inc(v_traceState_1753_);
lean_inc(v_auxDeclNGen_1752_);
lean_inc(v_ngen_1751_);
lean_inc(v_nextMacroScope_1750_);
lean_inc(v_env_1749_);
lean_dec(v___x_1746_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1771_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; 
lean_inc(v_openDecls_1748_);
lean_inc(v_currNamespace_1747_);
v___x_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1761_, 0, v_currNamespace_1747_);
lean_ctor_set(v___x_1761_, 1, v_openDecls_1748_);
v___x_1762_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
lean_ctor_set(v___x_1762_, 1, v___y_1741_);
lean_inc_ref(v___y_1740_);
lean_inc_ref(v___y_1743_);
v___x_1763_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1763_, 0, v___y_1743_);
lean_ctor_set(v___x_1763_, 1, v___y_1742_);
lean_ctor_set(v___x_1763_, 2, v___y_1737_);
lean_ctor_set(v___x_1763_, 3, v___y_1740_);
lean_ctor_set(v___x_1763_, 4, v___x_1762_);
lean_ctor_set_uint8(v___x_1763_, sizeof(void*)*5, v___y_1739_);
lean_ctor_set_uint8(v___x_1763_, sizeof(void*)*5 + 1, v___y_1738_);
lean_ctor_set_uint8(v___x_1763_, sizeof(void*)*5 + 2, v_isSilent_1730_);
v___x_1764_ = l_Lean_MessageLog_add(v___x_1763_, v_messages_1755_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 6, v___x_1764_);
v___x_1766_ = v___x_1759_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_env_1749_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_nextMacroScope_1750_);
lean_ctor_set(v_reuseFailAlloc_1770_, 2, v_ngen_1751_);
lean_ctor_set(v_reuseFailAlloc_1770_, 3, v_auxDeclNGen_1752_);
lean_ctor_set(v_reuseFailAlloc_1770_, 4, v_traceState_1753_);
lean_ctor_set(v_reuseFailAlloc_1770_, 5, v_cache_1754_);
lean_ctor_set(v_reuseFailAlloc_1770_, 6, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1770_, 7, v_infoState_1756_);
lean_ctor_set(v_reuseFailAlloc_1770_, 8, v_snapshotTasks_1757_);
v___x_1766_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = lean_st_ref_put(v___y_1745_, v___x_1766_);
v___x_1768_ = lean_box(0);
v___x_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
return v___x_1769_;
}
}
}
v___jp_1772_:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1796_; 
v___x_1781_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1728_);
v___x_1782_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v___x_1781_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1785_ = v___x_1782_;
v_isShared_1786_ = v_isSharedCheck_1796_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1782_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1796_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_inc_ref_n(v___y_1775_, 2);
v___x_1787_ = l_Lean_FileMap_toPosition(v___y_1775_, v___y_1774_);
lean_dec(v___y_1774_);
v___x_1788_ = l_Lean_FileMap_toPosition(v___y_1775_, v___y_1780_);
lean_dec(v___y_1780_);
v___x_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
v___x_1790_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___closed__0));
if (v___y_1777_ == 0)
{
lean_del_object(v___x_1785_);
lean_dec_ref(v___y_1773_);
v___y_1737_ = v___x_1789_;
v___y_1738_ = v___y_1778_;
v___y_1739_ = v___y_1776_;
v___y_1740_ = v___x_1790_;
v___y_1741_ = v_a_1783_;
v___y_1742_ = v___x_1787_;
v___y_1743_ = v___y_1779_;
v___y_1744_ = v___y_1733_;
v___y_1745_ = v___y_1734_;
goto v___jp_1736_;
}
else
{
uint8_t v___x_1791_; 
lean_inc(v_a_1783_);
v___x_1791_ = l_Lean_MessageData_hasTag(v___y_1773_, v_a_1783_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; lean_object* v___x_1794_; 
lean_dec_ref_known(v___x_1789_, 1);
lean_dec_ref(v___x_1787_);
lean_dec(v_a_1783_);
v___x_1792_ = lean_box(0);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v___x_1792_);
v___x_1794_ = v___x_1785_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1792_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
else
{
lean_del_object(v___x_1785_);
v___y_1737_ = v___x_1789_;
v___y_1738_ = v___y_1778_;
v___y_1739_ = v___y_1776_;
v___y_1740_ = v___x_1790_;
v___y_1741_ = v_a_1783_;
v___y_1742_ = v___x_1787_;
v___y_1743_ = v___y_1779_;
v___y_1744_ = v___y_1733_;
v___y_1745_ = v___y_1734_;
goto v___jp_1736_;
}
}
}
}
v___jp_1797_:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Lean_Syntax_getTailPos_x3f(v___y_1799_, v___y_1801_);
lean_dec(v___y_1799_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_inc(v___y_1805_);
v___y_1773_ = v___y_1798_;
v___y_1774_ = v___y_1805_;
v___y_1775_ = v___y_1800_;
v___y_1776_ = v___y_1801_;
v___y_1777_ = v___y_1802_;
v___y_1778_ = v___y_1803_;
v___y_1779_ = v___y_1804_;
v___y_1780_ = v___y_1805_;
goto v___jp_1772_;
}
else
{
lean_object* v_val_1807_; 
v_val_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_val_1807_);
lean_dec_ref_known(v___x_1806_, 1);
v___y_1773_ = v___y_1798_;
v___y_1774_ = v___y_1805_;
v___y_1775_ = v___y_1800_;
v___y_1776_ = v___y_1801_;
v___y_1777_ = v___y_1802_;
v___y_1778_ = v___y_1803_;
v___y_1779_ = v___y_1804_;
v___y_1780_ = v_val_1807_;
goto v___jp_1772_;
}
}
v___jp_1808_:
{
lean_object* v_ref_1816_; lean_object* v___x_1817_; 
v_ref_1816_ = l_Lean_replaceRef(v_ref_1727_, v___y_1810_);
v___x_1817_ = l_Lean_Syntax_getPos_x3f(v_ref_1816_, v___y_1812_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v___x_1818_; 
v___x_1818_ = lean_unsigned_to_nat(0u);
v___y_1798_ = v___y_1809_;
v___y_1799_ = v_ref_1816_;
v___y_1800_ = v___y_1811_;
v___y_1801_ = v___y_1812_;
v___y_1802_ = v___y_1813_;
v___y_1803_ = v___y_1815_;
v___y_1804_ = v___y_1814_;
v___y_1805_ = v___x_1818_;
goto v___jp_1797_;
}
else
{
lean_object* v_val_1819_; 
v_val_1819_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_val_1819_);
lean_dec_ref_known(v___x_1817_, 1);
v___y_1798_ = v___y_1809_;
v___y_1799_ = v_ref_1816_;
v___y_1800_ = v___y_1811_;
v___y_1801_ = v___y_1812_;
v___y_1802_ = v___y_1813_;
v___y_1803_ = v___y_1815_;
v___y_1804_ = v___y_1814_;
v___y_1805_ = v_val_1819_;
goto v___jp_1797_;
}
}
v___jp_1821_:
{
if (v___y_1828_ == 0)
{
v___y_1809_ = v___y_1825_;
v___y_1810_ = v___y_1822_;
v___y_1811_ = v___y_1823_;
v___y_1812_ = v___y_1827_;
v___y_1813_ = v___y_1824_;
v___y_1814_ = v___y_1826_;
v___y_1815_ = v_severity_1729_;
goto v___jp_1808_;
}
else
{
v___y_1809_ = v___y_1825_;
v___y_1810_ = v___y_1822_;
v___y_1811_ = v___y_1823_;
v___y_1812_ = v___y_1827_;
v___y_1813_ = v___y_1824_;
v___y_1814_ = v___y_1826_;
v___y_1815_ = v___x_1820_;
goto v___jp_1808_;
}
}
v___jp_1829_:
{
if (v___y_1830_ == 0)
{
lean_object* v_fileName_1831_; lean_object* v_fileMap_1832_; lean_object* v_options_1833_; lean_object* v_ref_1834_; uint8_t v_suppressElabErrors_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___f_1838_; uint8_t v___x_1839_; uint8_t v___x_1840_; 
v_fileName_1831_ = lean_ctor_get(v___y_1733_, 0);
v_fileMap_1832_ = lean_ctor_get(v___y_1733_, 1);
v_options_1833_ = lean_ctor_get(v___y_1733_, 2);
v_ref_1834_ = lean_ctor_get(v___y_1733_, 5);
v_suppressElabErrors_1835_ = lean_ctor_get_uint8(v___y_1733_, sizeof(void*)*14 + 1);
v___x_1836_ = lean_box(v___y_1830_);
v___x_1837_ = lean_box(v_suppressElabErrors_1835_);
v___f_1838_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1838_, 0, v___x_1836_);
lean_closure_set(v___f_1838_, 1, v___x_1837_);
v___x_1839_ = 1;
v___x_1840_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1729_, v___x_1839_);
if (v___x_1840_ == 0)
{
v___y_1822_ = v_ref_1834_;
v___y_1823_ = v_fileMap_1832_;
v___y_1824_ = v_suppressElabErrors_1835_;
v___y_1825_ = v___f_1838_;
v___y_1826_ = v_fileName_1831_;
v___y_1827_ = v___y_1830_;
v___y_1828_ = v___x_1840_;
goto v___jp_1821_;
}
else
{
lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1841_ = l_Lean_warningAsError;
v___x_1842_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_1833_, v___x_1841_);
v___y_1822_ = v_ref_1834_;
v___y_1823_ = v_fileMap_1832_;
v___y_1824_ = v_suppressElabErrors_1835_;
v___y_1825_ = v___f_1838_;
v___y_1826_ = v_fileName_1831_;
v___y_1827_ = v___y_1830_;
v___y_1828_ = v___x_1842_;
goto v___jp_1821_;
}
}
else
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
lean_dec_ref(v_msgData_1728_);
v___x_1843_ = lean_box(0);
v___x_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
return v___x_1844_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_1847_, lean_object* v_msgData_1848_, lean_object* v_severity_1849_, lean_object* v_isSilent_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
uint8_t v_severity_boxed_1856_; uint8_t v_isSilent_boxed_1857_; lean_object* v_res_1858_; 
v_severity_boxed_1856_ = lean_unbox(v_severity_1849_);
v_isSilent_boxed_1857_ = lean_unbox(v_isSilent_1850_);
v_res_1858_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(v_ref_1847_, v_msgData_1848_, v_severity_boxed_1856_, v_isSilent_boxed_1857_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v_ref_1847_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(lean_object* v_msgData_1859_, uint8_t v_severity_1860_, uint8_t v_isSilent_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_ref_1867_; lean_object* v___x_1868_; 
v_ref_1867_ = lean_ctor_get(v___y_1864_, 5);
v___x_1868_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(v_ref_1867_, v_msgData_1859_, v_severity_1860_, v_isSilent_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0___boxed(lean_object* v_msgData_1869_, lean_object* v_severity_1870_, lean_object* v_isSilent_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
uint8_t v_severity_boxed_1877_; uint8_t v_isSilent_boxed_1878_; lean_object* v_res_1879_; 
v_severity_boxed_1877_ = lean_unbox(v_severity_1870_);
v_isSilent_boxed_1878_ = lean_unbox(v_isSilent_1871_);
v_res_1879_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(v_msgData_1869_, v_severity_boxed_1877_, v_isSilent_boxed_1878_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(lean_object* v_msgData_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
uint8_t v___x_1886_; uint8_t v___x_1887_; lean_object* v___x_1888_; 
v___x_1886_ = 1;
v___x_1887_ = 0;
v___x_1888_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(v_msgData_1880_, v___x_1886_, v___x_1887_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0___boxed(lean_object* v_msgData_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(v_msgData_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
return v_res_1895_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__0));
v___x_1898_ = l_Lean_stringToMessageData(v___x_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0(uint8_t v___x_1899_, lean_object* v___x_1900_, lean_object* v___x_1901_, lean_object* v___x_1902_, lean_object* v___x_1903_, lean_object* v_tk_1904_, lean_object* v_typesStx_1905_, lean_object* v___x_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v_ref_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___y_1922_; 
v_ref_1912_ = lean_ctor_get(v___y_1909_, 5);
v___x_1913_ = l_Lean_SourceInfo_fromRef(v_ref_1912_, v___x_1899_);
v___x_1914_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__1));
v___x_1915_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__2));
v___x_1916_ = l_Lean_Name_mkStr4(v___x_1900_, v___x_1901_, v___x_1902_, v___x_1915_);
v___x_1917_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3));
lean_inc(v___x_1913_);
v___x_1918_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1913_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5));
v___x_1920_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6);
if (lean_obj_tag(v_typesStx_1905_) == 1)
{
lean_object* v_val_1943_; lean_object* v___x_1944_; 
v_val_1943_ = lean_ctor_get(v_typesStx_1905_, 0);
lean_inc(v_val_1943_);
lean_dec_ref_known(v_typesStx_1905_, 1);
v___x_1944_ = l_Array_mkArray1___redArg(v_val_1943_);
v___y_1922_ = v___x_1944_;
goto v___jp_1921_;
}
else
{
lean_object* v___x_1945_; 
lean_dec(v_typesStx_1905_);
v___x_1945_ = lean_mk_empty_array_with_capacity(v___x_1906_);
v___y_1922_ = v___x_1945_;
goto v___jp_1921_;
}
v___jp_1921_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1, &l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1);
v___x_1924_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(v___x_1923_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1941_; 
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1941_ == 0)
{
lean_object* v_unused_1942_; 
v_unused_1942_ = lean_ctor_get(v___x_1924_, 0);
lean_dec(v_unused_1942_);
v___x_1926_ = v___x_1924_;
v_isShared_1927_ = v_isSharedCheck_1941_;
goto v_resetjp_1925_;
}
else
{
lean_dec(v___x_1924_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1941_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1928_ = l_Array_append___redArg(v___x_1920_, v___y_1922_);
lean_dec_ref(v___y_1922_);
lean_inc(v___x_1913_);
v___x_1929_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1913_);
lean_ctor_set(v___x_1929_, 1, v___x_1919_);
lean_ctor_set(v___x_1929_, 2, v___x_1928_);
v___x_1930_ = l_Lean_Syntax_node3(v___x_1913_, v___x_1916_, v___x_1918_, v___x_1903_, v___x_1929_);
v___x_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1914_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = lean_box(0);
v___x_1933_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
lean_ctor_set(v___x_1933_, 2, v___x_1932_);
lean_ctor_set(v___x_1933_, 3, v___x_1932_);
lean_ctor_set(v___x_1933_, 4, v___x_1932_);
lean_ctor_set(v___x_1933_, 5, v___x_1932_);
lean_inc(v_ref_1912_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set_tag(v___x_1926_, 1);
lean_ctor_set(v___x_1926_, 0, v_ref_1912_);
v___x_1935_ = v___x_1926_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_ref_1912_);
v___x_1935_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1936_; uint8_t v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1936_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__7));
v___x_1937_ = 4;
v___x_1938_ = l_Lean_MessageData_nil;
v___x_1939_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1904_, v___x_1933_, v___x_1935_, v___x_1936_, v___x_1932_, v___x_1937_, v___x_1938_, v___y_1909_, v___y_1910_);
return v___x_1939_;
}
}
}
else
{
lean_dec_ref(v___y_1922_);
lean_dec_ref_known(v___x_1918_, 2);
lean_dec(v___x_1916_);
lean_dec(v___x_1913_);
lean_dec(v_tk_1904_);
lean_dec(v___x_1903_);
return v___x_1924_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___boxed(lean_object* v___x_1946_, lean_object* v___x_1947_, lean_object* v___x_1948_, lean_object* v___x_1949_, lean_object* v___x_1950_, lean_object* v_tk_1951_, lean_object* v_typesStx_1952_, lean_object* v___x_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
uint8_t v___x_8680__boxed_1959_; lean_object* v_res_1960_; 
v___x_8680__boxed_1959_ = lean_unbox(v___x_1946_);
v_res_1960_ = l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0(v___x_8680__boxed_1959_, v___x_1947_, v___x_1948_, v___x_1949_, v___x_1950_, v_tk_1951_, v_typesStx_1952_, v___x_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___x_1953_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic(lean_object* v_x_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; 
v___x_1979_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0));
v___x_1980_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1));
v___x_1981_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1));
v___x_1982_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0));
lean_inc(v_x_1969_);
v___x_1983_ = l_Lean_Syntax_isOfKind(v_x_1969_, v___x_1982_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; 
lean_dec(v_x_1969_);
v___x_1984_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1984_;
}
else
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1985_ = lean_unsigned_to_nat(1u);
v___x_1986_ = l_Lean_Syntax_getArg(v_x_1969_, v___x_1985_);
v___x_1987_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_1986_);
v___x_1988_ = l_Lean_Syntax_isOfKind(v___x_1986_, v___x_1987_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; 
lean_dec(v___x_1986_);
lean_dec(v_x_1969_);
v___x_1989_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1989_;
}
else
{
lean_object* v___x_1990_; lean_object* v_tk_1991_; lean_object* v_typesStx_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___x_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_1990_ = lean_unsigned_to_nat(0u);
v_tk_1991_ = l_Lean_Syntax_getArg(v_x_1969_, v___x_1990_);
v___x_2086_ = lean_unsigned_to_nat(2u);
v___x_2087_ = l_Lean_Syntax_getArg(v_x_1969_, v___x_2086_);
v___x_2088_ = l_Lean_Syntax_isNone(v___x_2087_);
if (v___x_2088_ == 0)
{
uint8_t v___x_2089_; 
lean_inc(v___x_2087_);
v___x_2089_ = l_Lean_Syntax_matchesNull(v___x_2087_, v___x_1985_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; 
lean_dec(v___x_2087_);
lean_dec(v_tk_1991_);
lean_dec(v___x_1986_);
lean_dec(v_x_1969_);
v___x_2090_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2090_;
}
else
{
lean_object* v_typesStx_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
v_typesStx_2091_ = l_Lean_Syntax_getArg(v___x_2087_, v___x_1990_);
lean_dec(v___x_2087_);
v___x_2092_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_typesStx_2091_);
v___x_2093_ = l_Lean_Syntax_isOfKind(v_typesStx_2091_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; 
lean_dec(v_typesStx_2091_);
lean_dec(v_tk_1991_);
lean_dec(v___x_1986_);
lean_dec(v_x_1969_);
v___x_2094_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2094_;
}
else
{
lean_object* v___x_2095_; 
v___x_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2095_, 0, v_typesStx_2091_);
v_typesStx_1993_ = v___x_2095_;
v___y_1994_ = v_a_1970_;
v___y_1995_ = v_a_1971_;
v___y_1996_ = v_a_1972_;
v___y_1997_ = v_a_1973_;
v___y_1998_ = v_a_1974_;
v___y_1999_ = v_a_1975_;
v___y_2000_ = v_a_1976_;
v___y_2001_ = v_a_1977_;
goto v___jp_1992_;
}
}
}
else
{
lean_object* v___x_2096_; 
lean_dec(v___x_2087_);
v___x_2096_ = lean_box(0);
v_typesStx_1993_ = v___x_2096_;
v___y_1994_ = v_a_1970_;
v___y_1995_ = v_a_1971_;
v___y_1996_ = v_a_1972_;
v___y_1997_ = v_a_1973_;
v___y_1998_ = v_a_1974_;
v___y_1999_ = v_a_1975_;
v___y_2000_ = v_a_1976_;
v___y_2001_ = v_a_1977_;
goto v___jp_1992_;
}
v___jp_1992_:
{
lean_object* v___x_2002_; lean_object* v_path_2003_; lean_object* v___x_2004_; uint8_t v___x_2005_; 
v___x_2002_ = lean_unsigned_to_nat(3u);
v_path_2003_ = l_Lean_Syntax_getArg(v_x_1969_, v___x_2002_);
lean_dec(v_x_1969_);
v___x_2004_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__2));
lean_inc(v_path_2003_);
v___x_2005_ = l_Lean_Syntax_isOfKind(v_path_2003_, v___x_2004_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; 
lean_dec(v_path_2003_);
lean_dec(v_typesStx_1993_);
lean_dec(v_tk_1991_);
lean_dec(v___x_1986_);
v___x_2006_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2006_;
}
else
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2084_; 
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2084_ == 0)
{
lean_object* v_unused_2085_; 
v_unused_2085_ = lean_ctor_get(v___x_2007_, 0);
lean_dec(v_unused_2085_);
v___x_2009_ = v___x_2007_;
v_isShared_2010_ = v_isSharedCheck_2084_;
goto v_resetjp_2008_;
}
else
{
lean_dec(v___x_2007_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2084_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2011_; uint8_t v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2011_ = lean_unsigned_to_nat(10u);
v___x_2012_ = 0;
v___x_2013_ = lean_unsigned_to_nat(100000u);
v___x_2014_ = 0;
v___x_2015_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_2015_, 0, v___x_2011_);
lean_ctor_set(v___x_2015_, 1, v___x_2013_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*2, v___x_1988_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*2 + 1, v___x_1988_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*2 + 2, v___x_2012_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*2 + 3, v___x_1988_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*2 + 4, v___x_1988_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*2 + 5, v___x_1988_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*2 + 6, v___x_1988_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*2 + 7, v___x_1988_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*2 + 8, v___x_2012_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*2 + 9, v___x_2012_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*2 + 10, v___x_2014_);
lean_inc(v___x_1986_);
v___x_2016_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_1986_, v___x_2015_, v___x_1988_, v___y_1994_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2018_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref_known(v___x_2016_, 1);
lean_inc(v_typesStx_1993_);
v___x_2018_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_1993_, v_a_2017_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
lean_dec_ref_known(v___x_2018_, 1);
v___x_2020_ = l_Lean_TSyntax_getString(v_path_2003_);
lean_dec(v_path_2003_);
v___x_2021_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v___x_2020_, v_a_2017_, v_a_2019_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2023_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___x_2021_, 1);
v___x_2023_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1995_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
v___x_2025_ = lean_unsigned_to_nat(9u);
v___x_2026_ = lean_unsigned_to_nat(5u);
v___x_2027_ = lean_unsigned_to_nat(8u);
v___x_2028_ = lean_unsigned_to_nat(1000u);
v___x_2029_ = lean_unsigned_to_nat(1024u);
v___x_2030_ = lean_unsigned_to_nat(10000u);
v___x_2031_ = lean_unsigned_to_nat(1048576u);
v___x_2032_ = lean_unsigned_to_nat(50u);
v___x_2033_ = lean_box(0);
v___x_2034_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_2034_, 0, v___x_2025_);
lean_ctor_set(v___x_2034_, 1, v___x_2026_);
lean_ctor_set(v___x_2034_, 2, v___x_2027_);
lean_ctor_set(v___x_2034_, 3, v___x_2027_);
lean_ctor_set(v___x_2034_, 4, v___x_2028_);
lean_ctor_set(v___x_2034_, 5, v___x_2028_);
lean_ctor_set(v___x_2034_, 6, v___x_2013_);
lean_ctor_set(v___x_2034_, 7, v___x_2029_);
lean_ctor_set(v___x_2034_, 8, v___x_2030_);
lean_ctor_set(v___x_2034_, 9, v___x_2028_);
lean_ctor_set(v___x_2034_, 10, v___x_2031_);
lean_ctor_set(v___x_2034_, 11, v___x_2011_);
lean_ctor_set(v___x_2034_, 12, v___x_2032_);
lean_ctor_set(v___x_2034_, 13, v___x_2033_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14, v___x_2012_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 1, v___x_2012_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 2, v___x_2012_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 3, v___x_2012_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 4, v___x_2012_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 5, v___x_1988_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 6, v___x_1988_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 7, v___x_1988_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 8, v___x_2012_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 9, v___x_2012_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 10, v___x_1988_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 11, v___x_2012_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 12, v___x_1988_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 13, v___x_1988_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 14, v___x_1988_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 15, v___x_1988_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 16, v___x_1988_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 17, v___x_2012_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 18, v___x_1988_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 19, v___x_1988_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 20, v___x_1988_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 21, v___x_1988_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 22, v___x_1988_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 23, v___x_1988_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 24, v___x_1988_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 25, v___x_1988_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 26, v___x_1988_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 27, v___x_1988_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 28, v___x_1988_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 29, v___x_1988_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 30, v___x_2012_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 31, v___x_1988_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*14 + 32, v___x_1988_);
v___x_2035_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_2034_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; lean_object* v___x_2037_; lean_object* v___f_2038_; lean_object* v___x_2040_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
lean_inc(v_a_2036_);
lean_dec_ref_known(v___x_2035_, 1);
v___x_2037_ = lean_box(v___x_2012_);
v___f_2038_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___boxed), 13, 8);
lean_closure_set(v___f_2038_, 0, v___x_2037_);
lean_closure_set(v___f_2038_, 1, v___x_1979_);
lean_closure_set(v___f_2038_, 2, v___x_1980_);
lean_closure_set(v___f_2038_, 3, v___x_1981_);
lean_closure_set(v___f_2038_, 4, v___x_1986_);
lean_closure_set(v___f_2038_, 5, v_tk_1991_);
lean_closure_set(v___f_2038_, 6, v_typesStx_1993_);
lean_closure_set(v___f_2038_, 7, v___x_1990_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v_a_2024_);
v___x_2040_ = v___x_2009_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2024_);
v___x_2040_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed), 13, 3);
lean_closure_set(v___x_2041_, 0, v___x_2040_);
lean_closure_set(v___x_2041_, 1, v_a_2022_);
lean_closure_set(v___x_2041_, 2, v___f_2038_);
v___x_2042_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___x_2041_, v_a_2036_, v___x_2033_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
return v___x_2042_;
}
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_dec(v_a_2024_);
lean_dec(v_a_2022_);
lean_del_object(v___x_2009_);
lean_dec(v_typesStx_1993_);
lean_dec(v_tk_1991_);
lean_dec(v___x_1986_);
v_a_2044_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_2035_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2035_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec(v_a_2022_);
lean_del_object(v___x_2009_);
lean_dec(v_typesStx_1993_);
lean_dec(v_tk_1991_);
lean_dec(v___x_1986_);
v_a_2052_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2023_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2023_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_del_object(v___x_2009_);
lean_dec(v_typesStx_1993_);
lean_dec(v_tk_1991_);
lean_dec(v___x_1986_);
v_a_2060_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2021_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2021_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec(v_a_2017_);
lean_del_object(v___x_2009_);
lean_dec(v_path_2003_);
lean_dec(v_typesStx_1993_);
lean_dec(v_tk_1991_);
lean_dec(v___x_1986_);
v_a_2068_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2018_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2018_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_del_object(v___x_2009_);
lean_dec(v_path_2003_);
lean_dec(v_typesStx_1993_);
lean_dec(v_tk_1991_);
lean_dec(v___x_1986_);
v_a_2076_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2016_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2016_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
}
else
{
lean_dec(v_path_2003_);
lean_dec(v_typesStx_1993_);
lean_dec(v_tk_1991_);
lean_dec(v___x_1986_);
return v___x_2007_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___boxed(lean_object* v_x_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic(v_x_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
lean_dec(v_a_2105_);
lean_dec_ref(v_a_2104_);
lean_dec(v_a_2103_);
lean_dec_ref(v_a_2102_);
lean_dec(v_a_2101_);
lean_dec_ref(v_a_2100_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1(){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2116_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2117_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0));
v___x_2118_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___closed__1));
v___x_2119_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___boxed), 10, 0);
v___x_2120_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2116_, v___x_2117_, v___x_2118_, v___x_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___boxed(lean_object* v_a_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1();
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0(lean_object* v___x_2123_, uint8_t v___x_2124_, lean_object* v___x_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2136_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2);
v___x_2137_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6);
v___x_2138_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__7));
v___x_2139_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2139_, 0, v___x_2136_);
lean_ctor_set(v___x_2139_, 1, v___x_2137_);
lean_ctor_set(v___x_2139_, 2, v___x_2123_);
lean_ctor_set(v___x_2139_, 3, v___x_2138_);
lean_ctor_set_uint8(v___x_2139_, sizeof(void*)*4, v___x_2124_);
v___x_2140_ = lean_st_mk_ref(v___x_2139_);
v___x_2141_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_2125_, v___x_2140_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2151_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2144_ = v___x_2141_;
v_isShared_2145_ = v_isSharedCheck_2151_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2141_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2151_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2149_; 
v___x_2146_ = lean_st_ref_get(v___x_2140_);
lean_dec(v___x_2140_);
v___x_2147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2147_, 0, v_a_2142_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 0, v___x_2147_);
v___x_2149_ = v___x_2144_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2147_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
lean_dec(v___x_2140_);
v_a_2152_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2141_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2141_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0___boxed(lean_object* v___x_2160_, lean_object* v___x_2161_, lean_object* v___x_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
uint8_t v___x_4600__boxed_2173_; lean_object* v_res_2174_; 
v___x_4600__boxed_2173_ = lean_unbox(v___x_2161_);
v_res_2174_ = l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0(v___x_2160_, v___x_4600__boxed_2173_, v___x_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___x_2162_);
return v_res_2174_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_2175_, lean_object* v_i_2176_, lean_object* v_k_2177_){
_start:
{
lean_object* v___x_2178_; uint8_t v___x_2179_; 
v___x_2178_ = lean_array_get_size(v_keys_2175_);
v___x_2179_ = lean_nat_dec_lt(v_i_2176_, v___x_2178_);
if (v___x_2179_ == 0)
{
lean_dec(v_i_2176_);
return v___x_2179_;
}
else
{
lean_object* v_k_x27_2180_; uint8_t v___x_2181_; 
v_k_x27_2180_ = lean_array_fget_borrowed(v_keys_2175_, v_i_2176_);
v___x_2181_ = l_Lean_instBEqMVarId_beq(v_k_2177_, v_k_x27_2180_);
if (v___x_2181_ == 0)
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2182_ = lean_unsigned_to_nat(1u);
v___x_2183_ = lean_nat_add(v_i_2176_, v___x_2182_);
lean_dec(v_i_2176_);
v_i_2176_ = v___x_2183_;
goto _start;
}
else
{
lean_dec(v_i_2176_);
return v___x_2181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_2185_, lean_object* v_i_2186_, lean_object* v_k_2187_){
_start:
{
uint8_t v_res_2188_; lean_object* v_r_2189_; 
v_res_2188_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2185_, v_i_2186_, v_k_2187_);
lean_dec(v_k_2187_);
lean_dec_ref(v_keys_2185_);
v_r_2189_ = lean_box(v_res_2188_);
return v_r_2189_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2190_, size_t v_x_2191_, lean_object* v_x_2192_){
_start:
{
if (lean_obj_tag(v_x_2190_) == 0)
{
lean_object* v_es_2193_; lean_object* v___x_2194_; size_t v___x_2195_; size_t v___x_2196_; lean_object* v_j_2197_; lean_object* v___x_2198_; 
v_es_2193_ = lean_ctor_get(v_x_2190_, 0);
v___x_2194_ = lean_box(2);
v___x_2195_ = ((size_t)31ULL);
v___x_2196_ = lean_usize_land(v_x_2191_, v___x_2195_);
v_j_2197_ = lean_usize_to_nat(v___x_2196_);
v___x_2198_ = lean_array_get_borrowed(v___x_2194_, v_es_2193_, v_j_2197_);
lean_dec(v_j_2197_);
switch(lean_obj_tag(v___x_2198_))
{
case 0:
{
lean_object* v_key_2199_; uint8_t v___x_2200_; 
v_key_2199_ = lean_ctor_get(v___x_2198_, 0);
v___x_2200_ = l_Lean_instBEqMVarId_beq(v_x_2192_, v_key_2199_);
return v___x_2200_;
}
case 1:
{
lean_object* v_node_2201_; size_t v___x_2202_; size_t v___x_2203_; 
v_node_2201_ = lean_ctor_get(v___x_2198_, 0);
v___x_2202_ = ((size_t)5ULL);
v___x_2203_ = lean_usize_shift_right(v_x_2191_, v___x_2202_);
v_x_2190_ = v_node_2201_;
v_x_2191_ = v___x_2203_;
goto _start;
}
default: 
{
uint8_t v___x_2205_; 
v___x_2205_ = 0;
return v___x_2205_;
}
}
}
else
{
lean_object* v_ks_2206_; lean_object* v___x_2207_; uint8_t v___x_2208_; 
v_ks_2206_ = lean_ctor_get(v_x_2190_, 0);
v___x_2207_ = lean_unsigned_to_nat(0u);
v___x_2208_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_2206_, v___x_2207_, v_x_2192_);
return v___x_2208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2209_, lean_object* v_x_2210_, lean_object* v_x_2211_){
_start:
{
size_t v_x_4705__boxed_2212_; uint8_t v_res_2213_; lean_object* v_r_2214_; 
v_x_4705__boxed_2212_ = lean_unbox_usize(v_x_2210_);
lean_dec(v_x_2210_);
v_res_2213_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_2209_, v_x_4705__boxed_2212_, v_x_2211_);
lean_dec(v_x_2211_);
lean_dec_ref(v_x_2209_);
v_r_2214_ = lean_box(v_res_2213_);
return v_r_2214_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(lean_object* v_x_2215_, lean_object* v_x_2216_){
_start:
{
uint64_t v___x_2217_; size_t v___x_2218_; uint8_t v___x_2219_; 
v___x_2217_ = l_Lean_instHashableMVarId_hash(v_x_2216_);
v___x_2218_ = lean_uint64_to_usize(v___x_2217_);
v___x_2219_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_2215_, v___x_2218_, v_x_2216_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_2220_, lean_object* v_x_2221_){
_start:
{
uint8_t v_res_2222_; lean_object* v_r_2223_; 
v_res_2222_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(v_x_2220_, v_x_2221_);
lean_dec(v_x_2221_);
lean_dec_ref(v_x_2220_);
v_r_2223_ = lean_box(v_res_2222_);
return v_r_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(lean_object* v_mvarId_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v___x_2227_; lean_object* v_mctx_2228_; lean_object* v_eAssignment_2229_; uint8_t v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2227_ = lean_st_ref_get(v___y_2225_);
v_mctx_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc_ref(v_mctx_2228_);
lean_dec(v___x_2227_);
v_eAssignment_2229_ = lean_ctor_get(v_mctx_2228_, 8);
lean_inc_ref(v_eAssignment_2229_);
lean_dec_ref(v_mctx_2228_);
v___x_2230_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(v_eAssignment_2229_, v_mvarId_2224_);
lean_dec_ref(v_eAssignment_2229_);
v___x_2231_ = lean_box(v___x_2230_);
v___x_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg___boxed(lean_object* v_mvarId_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(v_mvarId_2233_, v___y_2234_);
lean_dec(v___y_2234_);
lean_dec(v_mvarId_2233_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1(size_t v_sz_2237_, size_t v_i_2238_, lean_object* v_bs_2239_){
_start:
{
uint8_t v___x_2240_; 
v___x_2240_ = lean_usize_dec_lt(v_i_2238_, v_sz_2237_);
if (v___x_2240_ == 0)
{
return v_bs_2239_;
}
else
{
lean_object* v_v_2241_; lean_object* v_name_2242_; lean_object* v_type_2243_; lean_object* v_value_2244_; lean_object* v___x_2245_; lean_object* v_bs_x27_2246_; uint8_t v___x_2247_; uint8_t v___x_2248_; lean_object* v___x_2249_; size_t v___x_2250_; size_t v___x_2251_; lean_object* v___x_2252_; 
v_v_2241_ = lean_array_uget_borrowed(v_bs_2239_, v_i_2238_);
v_name_2242_ = lean_ctor_get(v_v_2241_, 0);
lean_inc(v_name_2242_);
v_type_2243_ = lean_ctor_get(v_v_2241_, 1);
lean_inc_ref(v_type_2243_);
v_value_2244_ = lean_ctor_get(v_v_2241_, 2);
lean_inc_ref(v_value_2244_);
v___x_2245_ = lean_unsigned_to_nat(0u);
v_bs_x27_2246_ = lean_array_uset(v_bs_2239_, v_i_2238_, v___x_2245_);
v___x_2247_ = 0;
v___x_2248_ = 0;
v___x_2249_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2249_, 0, v_name_2242_);
lean_ctor_set(v___x_2249_, 1, v_type_2243_);
lean_ctor_set(v___x_2249_, 2, v_value_2244_);
lean_ctor_set_uint8(v___x_2249_, sizeof(void*)*3, v___x_2247_);
lean_ctor_set_uint8(v___x_2249_, sizeof(void*)*3 + 1, v___x_2248_);
v___x_2250_ = ((size_t)1ULL);
v___x_2251_ = lean_usize_add(v_i_2238_, v___x_2250_);
v___x_2252_ = lean_array_uset(v_bs_x27_2246_, v_i_2238_, v___x_2249_);
v_i_2238_ = v___x_2251_;
v_bs_2239_ = v___x_2252_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1___boxed(lean_object* v_sz_2254_, lean_object* v_i_2255_, lean_object* v_bs_2256_){
_start:
{
size_t v_sz_boxed_2257_; size_t v_i_boxed_2258_; lean_object* v_res_2259_; 
v_sz_boxed_2257_ = lean_unbox_usize(v_sz_2254_);
lean_dec(v_sz_2254_);
v_i_boxed_2258_ = lean_unbox_usize(v_i_2255_);
lean_dec(v_i_2255_);
v_res_2259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1(v_sz_boxed_2257_, v_i_boxed_2258_, v_bs_2256_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize(lean_object* v_x_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_){
_start:
{
lean_object* v___x_2275_; uint8_t v___x_2276_; 
v___x_2275_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0));
lean_inc(v_x_2265_);
v___x_2276_ = l_Lean_Syntax_isOfKind(v_x_2265_, v___x_2275_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; 
lean_dec(v_x_2265_);
v___x_2277_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2277_;
}
else
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; uint8_t v___x_2281_; lean_object* v_types_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; 
v___x_2278_ = lean_unsigned_to_nat(1u);
v___x_2279_ = l_Lean_Syntax_getArg(v_x_2265_, v___x_2278_);
v___x_2280_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_2279_);
v___x_2281_ = l_Lean_Syntax_isOfKind(v___x_2279_, v___x_2280_);
if (v___x_2281_ == 0)
{
lean_object* v___x_2403_; 
lean_dec(v___x_2279_);
lean_dec(v_x_2265_);
v___x_2403_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2403_;
}
else
{
lean_object* v___x_2404_; lean_object* v___x_2405_; uint8_t v___x_2406_; 
v___x_2404_ = lean_unsigned_to_nat(2u);
v___x_2405_ = l_Lean_Syntax_getArg(v_x_2265_, v___x_2404_);
lean_dec(v_x_2265_);
v___x_2406_ = l_Lean_Syntax_isNone(v___x_2405_);
if (v___x_2406_ == 0)
{
uint8_t v___x_2407_; 
lean_inc(v___x_2405_);
v___x_2407_ = l_Lean_Syntax_matchesNull(v___x_2405_, v___x_2278_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2408_; 
lean_dec(v___x_2405_);
lean_dec(v___x_2279_);
v___x_2408_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2408_;
}
else
{
lean_object* v___x_2409_; lean_object* v_types_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; 
v___x_2409_ = lean_unsigned_to_nat(0u);
v_types_2410_ = l_Lean_Syntax_getArg(v___x_2405_, v___x_2409_);
lean_dec(v___x_2405_);
v___x_2411_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_types_2410_);
v___x_2412_ = l_Lean_Syntax_isOfKind(v_types_2410_, v___x_2411_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; 
lean_dec(v_types_2410_);
lean_dec(v___x_2279_);
v___x_2413_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2413_;
}
else
{
lean_object* v___x_2414_; 
v___x_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2414_, 0, v_types_2410_);
v_types_2283_ = v___x_2414_;
v___y_2284_ = v_a_2266_;
v___y_2285_ = v_a_2267_;
v___y_2286_ = v_a_2268_;
v___y_2287_ = v_a_2269_;
v___y_2288_ = v_a_2270_;
v___y_2289_ = v_a_2271_;
v___y_2290_ = v_a_2272_;
v___y_2291_ = v_a_2273_;
goto v___jp_2282_;
}
}
}
else
{
lean_object* v___x_2415_; 
lean_dec(v___x_2405_);
v___x_2415_ = lean_box(0);
v_types_2283_ = v___x_2415_;
v___y_2284_ = v_a_2266_;
v___y_2285_ = v_a_2267_;
v___y_2286_ = v_a_2268_;
v___y_2287_ = v_a_2269_;
v___y_2288_ = v_a_2270_;
v___y_2289_ = v_a_2271_;
v___y_2290_ = v_a_2272_;
v___y_2291_ = v_a_2273_;
goto v___jp_2282_;
}
}
v___jp_2282_:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_2290_, v___y_2291_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2401_; 
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2401_ == 0)
{
lean_object* v_unused_2402_; 
v_unused_2402_ = lean_ctor_get(v___x_2292_, 0);
lean_dec(v_unused_2402_);
v___x_2294_ = v___x_2292_;
v_isShared_2295_ = v_isSharedCheck_2401_;
goto v_resetjp_2293_;
}
else
{
lean_dec(v___x_2292_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2401_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2296_; uint8_t v___x_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2296_ = lean_unsigned_to_nat(10u);
v___x_2297_ = 0;
v___x_2298_ = lean_unsigned_to_nat(100000u);
v___x_2299_ = 0;
v___x_2300_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_2300_, 0, v___x_2296_);
lean_ctor_set(v___x_2300_, 1, v___x_2298_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*2, v___x_2281_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*2 + 1, v___x_2281_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*2 + 2, v___x_2297_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*2 + 3, v___x_2281_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*2 + 4, v___x_2281_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*2 + 5, v___x_2281_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*2 + 6, v___x_2281_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*2 + 7, v___x_2281_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*2 + 8, v___x_2297_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*2 + 9, v___x_2297_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*2 + 10, v___x_2299_);
v___x_2301_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_2279_, v___x_2300_, v___x_2281_, v___y_2284_, v___y_2290_, v___y_2291_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2303_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2302_);
lean_dec_ref_known(v___x_2301_, 1);
v___x_2303_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_types_2283_, v_a_2302_, v___y_2290_, v___y_2291_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2305_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2303_, 1);
v___x_2305_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2285_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2305_, 1);
v___x_2307_ = lean_unsigned_to_nat(9u);
v___x_2308_ = lean_unsigned_to_nat(5u);
v___x_2309_ = lean_unsigned_to_nat(8u);
v___x_2310_ = lean_unsigned_to_nat(1000u);
v___x_2311_ = lean_unsigned_to_nat(1024u);
v___x_2312_ = lean_unsigned_to_nat(10000u);
v___x_2313_ = lean_unsigned_to_nat(1048576u);
v___x_2314_ = lean_unsigned_to_nat(50u);
v___x_2315_ = lean_box(0);
v___x_2316_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_2316_, 0, v___x_2307_);
lean_ctor_set(v___x_2316_, 1, v___x_2308_);
lean_ctor_set(v___x_2316_, 2, v___x_2309_);
lean_ctor_set(v___x_2316_, 3, v___x_2309_);
lean_ctor_set(v___x_2316_, 4, v___x_2310_);
lean_ctor_set(v___x_2316_, 5, v___x_2310_);
lean_ctor_set(v___x_2316_, 6, v___x_2298_);
lean_ctor_set(v___x_2316_, 7, v___x_2311_);
lean_ctor_set(v___x_2316_, 8, v___x_2312_);
lean_ctor_set(v___x_2316_, 9, v___x_2310_);
lean_ctor_set(v___x_2316_, 10, v___x_2313_);
lean_ctor_set(v___x_2316_, 11, v___x_2296_);
lean_ctor_set(v___x_2316_, 12, v___x_2314_);
lean_ctor_set(v___x_2316_, 13, v___x_2315_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14, v___x_2297_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 1, v___x_2297_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 2, v___x_2297_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 3, v___x_2297_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 4, v___x_2297_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 5, v___x_2281_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 6, v___x_2281_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 7, v___x_2281_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 8, v___x_2297_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 9, v___x_2297_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 10, v___x_2281_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 11, v___x_2297_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 12, v___x_2281_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 13, v___x_2281_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 14, v___x_2281_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 15, v___x_2281_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 16, v___x_2281_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 17, v___x_2297_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 18, v___x_2281_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 19, v___x_2281_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 20, v___x_2281_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 21, v___x_2281_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 22, v___x_2281_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 23, v___x_2281_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 24, v___x_2281_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 25, v___x_2281_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 26, v___x_2281_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 27, v___x_2281_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 28, v___x_2281_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 29, v___x_2281_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 30, v___x_2297_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 31, v___x_2281_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*14 + 32, v___x_2281_);
v___x_2317_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_2316_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2320_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2318_);
lean_dec_ref_known(v___x_2317_, 1);
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v_a_2304_);
v___x_2320_ = v___x_2294_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2304_);
v___x_2320_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___f_2324_; lean_object* v___x_2325_; 
v___x_2321_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v___x_2320_, v_a_2302_);
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v_a_2306_);
v___x_2323_ = lean_box(v___x_2297_);
v___f_2324_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0___boxed), 13, 3);
lean_closure_set(v___f_2324_, 0, v___x_2322_);
lean_closure_set(v___f_2324_, 1, v___x_2323_);
lean_closure_set(v___f_2324_, 2, v___x_2321_);
v___x_2325_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___f_2324_, v_a_2318_, v___x_2315_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v_snd_2327_; lean_object* v_target_2328_; lean_object* v_hypotheses_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v_a_2332_; uint8_t v___x_2333_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
lean_dec_ref_known(v___x_2325_, 1);
v_snd_2327_ = lean_ctor_get(v_a_2326_, 1);
lean_inc(v_snd_2327_);
lean_dec(v_a_2326_);
v_target_2328_ = lean_ctor_get(v_snd_2327_, 2);
lean_inc_ref(v_target_2328_);
v_hypotheses_2329_ = lean_ctor_get(v_snd_2327_, 3);
lean_inc_ref(v_hypotheses_2329_);
lean_dec(v_snd_2327_);
v___x_2330_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_2328_);
lean_dec_ref(v_target_2328_);
v___x_2331_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(v___x_2330_, v___y_2289_);
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref(v___x_2331_);
v___x_2333_ = lean_unbox(v_a_2332_);
lean_dec(v_a_2332_);
if (v___x_2333_ == 0)
{
size_t v_sz_2334_; size_t v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v_sz_2334_ = lean_array_size(v_hypotheses_2329_);
v___x_2335_ = ((size_t)0ULL);
v___x_2336_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1(v_sz_2334_, v___x_2335_, v_hypotheses_2329_);
v___x_2337_ = l_Lean_MVarId_assertHypotheses(v___x_2330_, v___x_2336_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v_snd_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2348_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v_snd_2339_ = lean_ctor_get(v_a_2338_, 1);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_a_2338_);
if (v_isSharedCheck_2348_ == 0)
{
lean_object* v_unused_2349_; 
v_unused_2349_ = lean_ctor_get(v_a_2338_, 0);
lean_dec(v_unused_2349_);
v___x_2341_ = v_a_2338_;
v_isShared_2342_ = v_isSharedCheck_2348_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_snd_2339_);
lean_dec(v_a_2338_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2348_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2343_; lean_object* v___x_2345_; 
v___x_2343_ = lean_box(0);
if (v_isShared_2342_ == 0)
{
lean_ctor_set_tag(v___x_2341_, 1);
lean_ctor_set(v___x_2341_, 1, v___x_2343_);
lean_ctor_set(v___x_2341_, 0, v_snd_2339_);
v___x_2345_ = v___x_2341_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_snd_2339_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v___x_2343_);
v___x_2345_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2345_, v___y_2285_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
return v___x_2346_;
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
v_a_2350_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2337_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2337_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
else
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
lean_dec(v___x_2330_);
lean_dec_ref(v_hypotheses_2329_);
v___x_2358_ = lean_box(0);
v___x_2359_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2358_, v___y_2285_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
return v___x_2359_;
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
v_a_2360_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2325_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2325_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
lean_dec(v_a_2306_);
lean_dec(v_a_2304_);
lean_dec(v_a_2302_);
lean_del_object(v___x_2294_);
v_a_2369_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2317_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2317_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
lean_dec(v_a_2304_);
lean_dec(v_a_2302_);
lean_del_object(v___x_2294_);
v_a_2377_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2305_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2305_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
lean_dec(v_a_2302_);
lean_del_object(v___x_2294_);
v_a_2385_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2303_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2303_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
else
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
lean_del_object(v___x_2294_);
lean_dec(v_types_2283_);
v_a_2393_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2301_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2301_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
}
else
{
lean_dec(v_types_2283_);
lean_dec(v___x_2279_);
return v___x_2292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___boxed(lean_object* v_x_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_Elab_Tactic_BVDecide_evalBVNormalize(v_x_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
lean_dec(v_a_2424_);
lean_dec_ref(v_a_2423_);
lean_dec(v_a_2422_);
lean_dec_ref(v_a_2421_);
lean_dec(v_a_2420_);
lean_dec_ref(v_a_2419_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0(lean_object* v_mvarId_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v___x_2437_; 
v___x_2437_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(v_mvarId_2427_, v___y_2433_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___boxed(lean_object* v_mvarId_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0(v_mvarId_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v_mvarId_2438_);
return v_res_2448_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0(lean_object* v_00_u03b2_2449_, lean_object* v_x_2450_, lean_object* v_x_2451_){
_start:
{
uint8_t v___x_2452_; 
v___x_2452_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(v_x_2450_, v_x_2451_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2453_, lean_object* v_x_2454_, lean_object* v_x_2455_){
_start:
{
uint8_t v_res_2456_; lean_object* v_r_2457_; 
v_res_2456_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0(v_00_u03b2_2453_, v_x_2454_, v_x_2455_);
lean_dec(v_x_2455_);
lean_dec_ref(v_x_2454_);
v_r_2457_ = lean_box(v_res_2456_);
return v_r_2457_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2458_, lean_object* v_x_2459_, size_t v_x_2460_, lean_object* v_x_2461_){
_start:
{
uint8_t v___x_2462_; 
v___x_2462_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_2459_, v_x_2460_, v_x_2461_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2463_, lean_object* v_x_2464_, lean_object* v_x_2465_, lean_object* v_x_2466_){
_start:
{
size_t v_x_5140__boxed_2467_; uint8_t v_res_2468_; lean_object* v_r_2469_; 
v_x_5140__boxed_2467_ = lean_unbox_usize(v_x_2465_);
lean_dec(v_x_2465_);
v_res_2468_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1(v_00_u03b2_2463_, v_x_2464_, v_x_5140__boxed_2467_, v_x_2466_);
lean_dec(v_x_2466_);
lean_dec_ref(v_x_2464_);
v_r_2469_ = lean_box(v_res_2468_);
return v_r_2469_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2470_, lean_object* v_keys_2471_, lean_object* v_vals_2472_, lean_object* v_heq_2473_, lean_object* v_i_2474_, lean_object* v_k_2475_){
_start:
{
uint8_t v___x_2476_; 
v___x_2476_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2471_, v_i_2474_, v_k_2475_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2477_, lean_object* v_keys_2478_, lean_object* v_vals_2479_, lean_object* v_heq_2480_, lean_object* v_i_2481_, lean_object* v_k_2482_){
_start:
{
uint8_t v_res_2483_; lean_object* v_r_2484_; 
v_res_2483_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2477_, v_keys_2478_, v_vals_2479_, v_heq_2480_, v_i_2481_, v_k_2482_);
lean_dec(v_k_2482_);
lean_dec_ref(v_vals_2479_);
lean_dec_ref(v_keys_2478_);
v_r_2484_ = lean_box(v_res_2483_);
return v_r_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1(){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2493_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2494_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0));
v___x_2495_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___closed__1));
v___x_2496_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___boxed), 10, 0);
v___x_2497_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2493_, v___x_2494_, v___x_2495_, v___x_2496_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___boxed(lean_object* v_a_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1();
return v_res_2499_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_TacticContext(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_TacticContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide(builtin);
}
#ifdef __cplusplus
}
#endif
