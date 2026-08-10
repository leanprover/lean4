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
lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkDefaultParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
static const lean_array_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value;
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
v___x_6_ = lean_alloc_ctor(0, 10, 0);
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
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_box(0);
v___x_421_ = lean_unsigned_to_nat(16u);
v___x_422_ = lean_mk_array(v___x_421_, v___x_420_);
return v___x_422_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_423_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2);
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v___x_423_);
return v___x_425_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3);
v___x_427_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
lean_ctor_set(v___x_427_, 2, v___x_426_);
lean_ctor_set(v___x_427_, 3, v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck(lean_object* v_target_430_, lean_object* v_ctx_431_, lean_object* v_warn_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___y_450_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_443_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1);
v___x_444_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4);
v___x_445_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5));
v___x_446_ = 0;
v___x_447_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_447_, 0, v___x_443_);
lean_ctor_set(v___x_447_, 1, v___x_443_);
lean_ctor_set(v___x_447_, 2, v___x_443_);
lean_ctor_set(v___x_447_, 3, v___x_444_);
lean_ctor_set(v___x_447_, 4, v_target_430_);
lean_ctor_set(v___x_447_, 5, v___x_445_);
lean_ctor_set_uint8(v___x_447_, sizeof(void*)*6, v___x_446_);
v___x_448_ = lean_st_mk_ref(v___x_447_);
v___x_460_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_ctx_431_);
v___x_461_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_460_, v___x_448_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
lean_dec_ref(v___x_460_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; uint8_t v___x_463_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_a_462_);
lean_dec_ref_known(v___x_461_, 1);
v___x_463_ = lean_unbox(v_a_462_);
lean_dec(v_a_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v_target_466_; lean_object* v_hypotheses_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec_ref(v_warn_432_);
v___x_464_ = lean_st_ref_get(v___x_448_);
v___x_465_ = lean_st_ref_get(v___x_448_);
v_target_466_ = lean_ctor_get(v___x_464_, 4);
lean_inc_ref(v_target_466_);
lean_dec(v___x_464_);
v_hypotheses_467_ = lean_ctor_get(v___x_465_, 5);
lean_inc_ref(v_hypotheses_467_);
lean_dec(v___x_465_);
v___x_468_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_466_);
lean_dec_ref(v_target_466_);
v___x_469_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(v___x_468_, v_hypotheses_467_, v_ctx_431_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
v___y_450_ = v___x_469_;
goto v___jp_449_;
}
else
{
lean_object* v___x_470_; 
lean_dec_ref(v_ctx_431_);
lean_inc(v_a_441_);
lean_inc_ref(v_a_440_);
lean_inc(v_a_439_);
lean_inc_ref(v_a_438_);
v___x_470_ = lean_apply_5(v_warn_432_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, lean_box(0));
v___y_450_ = v___x_470_;
goto v___jp_449_;
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_dec(v___x_448_);
lean_dec_ref(v_warn_432_);
lean_dec_ref(v_ctx_431_);
v_a_471_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_461_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_461_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
v___jp_449_:
{
if (lean_obj_tag(v___y_450_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_459_; 
v_a_451_ = lean_ctor_get(v___y_450_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___y_450_);
if (v_isSharedCheck_459_ == 0)
{
v___x_453_ = v___y_450_;
v_isShared_454_ = v_isSharedCheck_459_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___y_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_459_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; lean_object* v___x_457_; 
v___x_455_ = lean_st_ref_get(v___x_448_);
lean_dec(v___x_448_);
lean_dec(v___x_455_);
if (v_isShared_454_ == 0)
{
v___x_457_ = v___x_453_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_451_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
else
{
lean_dec(v___x_448_);
return v___y_450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed(lean_object* v_target_479_, lean_object* v_ctx_480_, lean_object* v_warn_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck(v_target_479_, v_ctx_480_, v_warn_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(lean_object* v___y_493_){
_start:
{
lean_object* v_ref_495_; uint8_t v___x_496_; lean_object* v___x_497_; 
v_ref_495_ = lean_ctor_get(v___y_493_, 5);
v___x_496_ = 0;
v___x_497_ = l_Lean_Syntax_getPos_x3f(v_ref_495_, v___x_496_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
else
{
lean_object* v_val_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
v_val_500_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_497_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_val_500_);
lean_dec(v___x_497_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
lean_ctor_set_tag(v___x_502_, 0);
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_val_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg___boxed(lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v___y_508_);
lean_dec_ref(v___y_508_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0(lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v___y_515_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___boxed(lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0(v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
return v_res_526_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__2));
v___x_531_ = l_Lean_stringToMessageData(v___x_530_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__4));
v___x_534_ = l_Lean_stringToMessageData(v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_fileName_542_; lean_object* v_fileMap_543_; lean_object* v___x_544_; 
v_fileName_542_ = lean_ctor_get(v_a_539_, 0);
v_fileMap_543_ = lean_ctor_get(v_a_539_, 1);
lean_inc_ref(v_fileName_542_);
v___x_544_ = l_System_FilePath_fileName(v_fileName_542_);
if (lean_obj_tag(v___x_544_) == 1)
{
lean_object* v_val_545_; lean_object* v___x_546_; 
v_val_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_val_545_);
lean_dec_ref_known(v___x_544_, 1);
v___x_546_ = l_Lean_Elab_Term_getDeclName_x3f___redArg(v_a_535_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___x_546_, 1);
if (lean_obj_tag(v_a_547_) == 1)
{
lean_object* v_val_548_; lean_object* v___x_549_; lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_573_; 
v_val_548_ = lean_ctor_get(v_a_547_, 0);
lean_inc(v_val_548_);
lean_dec_ref_known(v_a_547_, 1);
v___x_549_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v_a_539_);
v_a_550_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_573_ == 0)
{
v___x_552_ = v___x_549_;
v_isShared_553_ = v_isSharedCheck_573_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_573_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v_line_555_; lean_object* v_column_556_; lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_571_; 
lean_inc_ref(v_fileMap_543_);
v___x_554_ = l_Lean_FileMap_toPosition(v_fileMap_543_, v_a_550_);
lean_dec(v_a_550_);
v_line_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_line_555_);
v_column_556_ = lean_ctor_get(v___x_554_, 1);
lean_inc(v_column_556_);
lean_dec_ref(v___x_554_);
v___x_557_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__0));
v___x_558_ = lean_string_append(v_val_545_, v___x_557_);
v___x_559_ = 1;
v___x_560_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_548_, v___x_559_);
v___x_561_ = lean_string_append(v___x_558_, v___x_560_);
lean_dec_ref(v___x_560_);
v___x_562_ = lean_string_append(v___x_561_, v___x_557_);
v___x_563_ = l_Nat_reprFast(v_line_555_);
v___x_564_ = lean_string_append(v___x_562_, v___x_563_);
lean_dec_ref(v___x_563_);
v___x_565_ = lean_string_append(v___x_564_, v___x_557_);
v___x_566_ = l_Nat_reprFast(v_column_556_);
v___x_567_ = lean_string_append(v___x_565_, v___x_566_);
lean_dec_ref(v___x_566_);
v___x_568_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__1));
v___x_569_ = lean_string_append(v___x_567_, v___x_568_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_569_);
v___x_571_ = v___x_552_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec(v_a_547_);
lean_dec(v_val_545_);
v___x_574_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3, &l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3);
v___x_575_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v___x_574_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
return v___x_575_;
}
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec(v_val_545_);
v_a_576_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_546_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_546_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec(v___x_544_);
v___x_584_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5, &l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5);
v___x_585_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v___x_584_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___boxed(lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec(v_a_587_);
lean_dec_ref(v_a_586_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(lean_object* v_cfg_594_, lean_object* v_types_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; lean_object* v___x_605_; 
v_a_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_a_604_);
lean_dec_ref_known(v___x_603_, 1);
v___x_605_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v_a_604_, v_cfg_594_, v_types_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
return v___x_605_;
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec(v_types_595_);
lean_dec_ref(v_cfg_594_);
v_a_606_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_603_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_603_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext___boxed(lean_object* v_cfg_614_, lean_object* v_types_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(v_cfg_614_, v_types_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorIdx(lean_object* v_x_624_){
_start:
{
if (lean_obj_tag(v_x_624_) == 0)
{
lean_object* v___x_625_; 
v___x_625_ = lean_unsigned_to_nat(0u);
return v___x_625_;
}
else
{
lean_object* v___x_626_; 
v___x_626_ = lean_unsigned_to_nat(1u);
return v___x_626_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorIdx___boxed(lean_object* v_x_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorIdx(v_x_627_);
lean_dec(v_x_627_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(lean_object* v_t_629_, lean_object* v_k_630_){
_start:
{
if (lean_obj_tag(v_t_629_) == 0)
{
return v_k_630_;
}
else
{
lean_object* v_path_631_; lean_object* v___x_632_; 
v_path_631_ = lean_ctor_get(v_t_629_, 0);
lean_inc_ref(v_path_631_);
lean_dec_ref_known(v_t_629_, 1);
v___x_632_ = lean_apply_1(v_k_630_, v_path_631_);
return v___x_632_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim(lean_object* v_motive_633_, lean_object* v_ctorIdx_634_, lean_object* v_t_635_, lean_object* v_h_636_, lean_object* v_k_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_635_, v_k_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___boxed(lean_object* v_motive_639_, lean_object* v_ctorIdx_640_, lean_object* v_t_641_, lean_object* v_h_642_, lean_object* v_k_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim(v_motive_639_, v_ctorIdx_640_, v_t_641_, v_h_642_, v_k_643_);
lean_dec(v_ctorIdx_640_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_normalize_elim___redArg(lean_object* v_t_645_, lean_object* v_normalize_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_645_, v_normalize_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_normalize_elim(lean_object* v_motive_648_, lean_object* v_t_649_, lean_object* v_h_650_, lean_object* v_normalize_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_649_, v_normalize_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_check_elim___redArg(lean_object* v_t_653_, lean_object* v_check_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_653_, v_check_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_check_elim(lean_object* v_motive_656_, lean_object* v_t_657_, lean_object* v_h_658_, lean_object* v_check_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_657_, v_check_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0(lean_object* v_x_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v___x_672_; 
lean_inc(v___y_666_);
lean_inc_ref(v___y_665_);
lean_inc(v___y_664_);
lean_inc_ref(v___y_663_);
lean_inc(v___y_662_);
v___x_672_ = lean_apply_10(v_x_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, lean_box(0));
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0___boxed(lean_object* v_x_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0(v_x_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(lean_object* v_mvarId_685_, lean_object* v_x_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v___f_697_; lean_object* v___x_698_; 
lean_inc(v___y_691_);
lean_inc_ref(v___y_690_);
lean_inc(v___y_689_);
lean_inc_ref(v___y_688_);
lean_inc(v___y_687_);
v___f_697_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_697_, 0, v_x_686_);
lean_closure_set(v___f_697_, 1, v___y_687_);
lean_closure_set(v___f_697_, 2, v___y_688_);
lean_closure_set(v___f_697_, 3, v___y_689_);
lean_closure_set(v___f_697_, 4, v___y_690_);
lean_closure_set(v___f_697_, 5, v___y_691_);
v___x_698_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_685_, v___f_697_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
if (lean_obj_tag(v___x_698_) == 0)
{
return v___x_698_;
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_698_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_698_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___boxed(lean_object* v_mvarId_707_, lean_object* v_x_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v_mvarId_707_, v_x_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1(lean_object* v_00_u03b1_720_, lean_object* v_mvarId_721_, lean_object* v_x_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v_mvarId_721_, v_x_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___boxed(lean_object* v_00_u03b1_734_, lean_object* v_mvarId_735_, lean_object* v_x_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1(v_00_u03b1_734_, v_mvarId_735_, v_x_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(lean_object* v_e_748_){
_start:
{
if (lean_obj_tag(v_e_748_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_758_; 
v_a_750_ = lean_ctor_get(v_e_748_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v_e_748_);
if (v_isSharedCheck_758_ == 0)
{
v___x_752_ = v_e_748_;
v_isShared_753_ = v_isSharedCheck_758_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v_e_748_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_758_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_754_ = lean_mk_io_user_error(v_a_750_);
if (v_isShared_753_ == 0)
{
lean_ctor_set_tag(v___x_752_, 1);
lean_ctor_set(v___x_752_, 0, v___x_754_);
v___x_756_ = v___x_752_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
v_a_759_ = lean_ctor_get(v_e_748_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v_e_748_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v_e_748_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v_e_748_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set_tag(v___x_761_, 0);
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg___boxed(lean_object* v_e_767_, lean_object* v_a_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v_e_767_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2(lean_object* v_00_u03b1_770_, lean_object* v_e_771_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v_e_771_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___boxed(lean_object* v_00_u03b1_774_, lean_object* v_e_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2(v_00_u03b1_774_, v_e_775_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(lean_object* v_msg_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_ref_784_; lean_object* v___x_785_; lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_794_; 
v_ref_784_ = lean_ctor_get(v___y_781_, 5);
v___x_785_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v_msg_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_794_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_794_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_794_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_792_; 
lean_inc(v_ref_784_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v_ref_784_);
lean_ctor_set(v___x_790_, 1, v_a_786_);
if (v_isShared_789_ == 0)
{
lean_ctor_set_tag(v___x_788_, 1);
lean_ctor_set(v___x_788_, 0, v___x_790_);
v___x_792_ = v___x_788_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg___boxed(lean_object* v_msg_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(v_msg_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(lean_object* v_target_802_, lean_object* v_ctx_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_exprDef_814_; lean_object* v_certDef_815_; lean_object* v_reflectionDef_816_; lean_object* v_solver_817_; lean_object* v_lratPath_818_; lean_object* v_config_819_; lean_object* v_restrictedTypes_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_946_; 
v_exprDef_814_ = lean_ctor_get(v_ctx_803_, 0);
v_certDef_815_ = lean_ctor_get(v_ctx_803_, 1);
v_reflectionDef_816_ = lean_ctor_get(v_ctx_803_, 2);
v_solver_817_ = lean_ctor_get(v_ctx_803_, 3);
v_lratPath_818_ = lean_ctor_get(v_ctx_803_, 4);
v_config_819_ = lean_ctor_get(v_ctx_803_, 5);
v_restrictedTypes_820_ = lean_ctor_get(v_ctx_803_, 6);
v_isSharedCheck_946_ = !lean_is_exclusive(v_ctx_803_);
if (v_isSharedCheck_946_ == 0)
{
v___x_822_ = v_ctx_803_;
v_isShared_823_ = v_isSharedCheck_946_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_restrictedTypes_820_);
lean_inc(v_config_819_);
lean_inc(v_lratPath_818_);
lean_inc(v_solver_817_);
lean_inc(v_reflectionDef_816_);
lean_inc(v_certDef_815_);
lean_inc(v_exprDef_814_);
lean_dec(v_ctx_803_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_946_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v_timeout_846_; uint8_t v_trimProofs_847_; uint8_t v_binaryProofs_848_; uint8_t v_acNf_849_; uint8_t v_andFlattening_850_; uint8_t v_embeddedConstraintSubst_851_; uint8_t v_structures_852_; uint8_t v_fixedInt_853_; uint8_t v_enums_854_; uint8_t v_graphviz_855_; lean_object* v_maxSteps_856_; uint8_t v_shortCircuit_857_; uint8_t v_solverMode_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_945_; 
v_timeout_846_ = lean_ctor_get(v_config_819_, 0);
v_trimProofs_847_ = lean_ctor_get_uint8(v_config_819_, sizeof(void*)*2);
v_binaryProofs_848_ = lean_ctor_get_uint8(v_config_819_, sizeof(void*)*2 + 1);
v_acNf_849_ = lean_ctor_get_uint8(v_config_819_, sizeof(void*)*2 + 2);
v_andFlattening_850_ = lean_ctor_get_uint8(v_config_819_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_851_ = lean_ctor_get_uint8(v_config_819_, sizeof(void*)*2 + 4);
v_structures_852_ = lean_ctor_get_uint8(v_config_819_, sizeof(void*)*2 + 5);
v_fixedInt_853_ = lean_ctor_get_uint8(v_config_819_, sizeof(void*)*2 + 6);
v_enums_854_ = lean_ctor_get_uint8(v_config_819_, sizeof(void*)*2 + 7);
v_graphviz_855_ = lean_ctor_get_uint8(v_config_819_, sizeof(void*)*2 + 8);
v_maxSteps_856_ = lean_ctor_get(v_config_819_, 1);
v_shortCircuit_857_ = lean_ctor_get_uint8(v_config_819_, sizeof(void*)*2 + 9);
v_solverMode_858_ = lean_ctor_get_uint8(v_config_819_, sizeof(void*)*2 + 10);
v_isSharedCheck_945_ = !lean_is_exclusive(v_config_819_);
if (v_isSharedCheck_945_ == 0)
{
v___x_860_ = v_config_819_;
v_isShared_861_ = v_isSharedCheck_945_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_maxSteps_856_);
lean_inc(v_timeout_846_);
lean_dec(v_config_819_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_945_;
goto v_resetjp_859_;
}
v___jp_824_:
{
lean_object* v___x_834_; 
v___x_834_ = l_System_FilePath_fileName(v_lratPath_818_);
if (lean_obj_tag(v___x_834_) == 1)
{
lean_object* v_val_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_843_; 
v_val_835_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_843_ == 0)
{
v___x_837_ = v___x_834_;
v_isShared_838_ = v_isSharedCheck_843_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_val_835_);
lean_dec(v___x_834_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_843_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_val_835_);
v___x_840_ = v_reuseFailAlloc_842_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_841_; 
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
}
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; 
lean_dec(v___x_834_);
v___x_844_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5, &l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5);
v___x_845_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(v___x_844_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
return v___x_845_;
}
}
v_resetjp_859_:
{
lean_object* v___x_862_; uint8_t v___x_863_; lean_object* v___x_865_; 
v___x_862_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_802_);
v___x_863_ = 0;
if (v_isShared_861_ == 0)
{
v___x_865_ = v___x_860_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_timeout_846_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_maxSteps_856_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*2 + 1, v_binaryProofs_848_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*2 + 2, v_acNf_849_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*2 + 3, v_andFlattening_850_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_851_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*2 + 5, v_structures_852_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*2 + 6, v_fixedInt_853_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*2 + 7, v_enums_854_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*2 + 8, v_graphviz_855_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*2 + 9, v_shortCircuit_857_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*2 + 10, v_solverMode_858_);
v___x_865_ = v_reuseFailAlloc_944_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_867_; 
lean_ctor_set_uint8(v___x_865_, sizeof(void*)*2, v___x_863_);
lean_inc_ref(v_lratPath_818_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 5, v___x_865_);
v___x_867_ = v___x_822_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_exprDef_814_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_certDef_815_);
lean_ctor_set(v_reuseFailAlloc_943_, 2, v_reflectionDef_816_);
lean_ctor_set(v_reuseFailAlloc_943_, 3, v_solver_817_);
lean_ctor_set(v_reuseFailAlloc_943_, 4, v_lratPath_818_);
lean_ctor_set(v_reuseFailAlloc_943_, 5, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_943_, 6, v_restrictedTypes_820_);
v___x_867_ = v_reuseFailAlloc_943_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed), 12, 2);
lean_closure_set(v___x_868_, 0, v_target_802_);
lean_closure_set(v___x_868_, 1, v___x_867_);
v___x_869_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v___x_862_, v___x_868_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_934_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_934_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_934_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_934_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
if (lean_obj_tag(v_a_870_) == 0)
{
lean_object* v___x_874_; lean_object* v___x_876_; 
lean_dec_ref(v_lratPath_818_);
v___x_874_ = lean_box(0);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_874_);
v___x_876_ = v___x_872_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
else
{
lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_932_; 
lean_del_object(v___x_872_);
v_isSharedCheck_932_ = !lean_is_exclusive(v_a_870_);
if (v_isSharedCheck_932_ == 0)
{
lean_object* v_unused_933_; 
v_unused_933_ = lean_ctor_get(v_a_870_, 0);
lean_dec(v_unused_933_);
v___x_879_ = v_a_870_;
v_isShared_880_ = v_isSharedCheck_932_;
goto v_resetjp_878_;
}
else
{
lean_dec(v_a_870_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_932_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
if (v_trimProofs_847_ == 0)
{
lean_del_object(v___x_879_);
v___y_825_ = v_a_804_;
v___y_826_ = v_a_805_;
v___y_827_ = v_a_806_;
v___y_828_ = v_a_807_;
v___y_829_ = v_a_808_;
v___y_830_ = v_a_809_;
v___y_831_ = v_a_810_;
v___y_832_ = v_a_811_;
v___y_833_ = v_a_812_;
goto v___jp_824_;
}
else
{
lean_object* v___x_881_; 
v___x_881_ = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(v_lratPath_818_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_881_, 1);
v___x_883_ = l_Lean_Meta_Tactic_BVDecide_LRAT_trim(v_a_882_);
lean_dec(v_a_882_);
v___x_884_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v___x_883_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_886_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref_known(v___x_884_, 1);
v___x_886_ = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(v_lratPath_818_, v_a_885_, v_binaryProofs_848_);
lean_dec(v_a_885_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_dec_ref_known(v___x_886_, 1);
lean_del_object(v___x_879_);
v___y_825_ = v_a_804_;
v___y_826_ = v_a_805_;
v___y_827_ = v_a_806_;
v___y_828_ = v_a_807_;
v___y_829_ = v_a_808_;
v___y_830_ = v_a_809_;
v___y_831_ = v_a_810_;
v___y_832_ = v_a_811_;
v___y_833_ = v_a_812_;
goto v___jp_824_;
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_901_; 
lean_dec_ref(v_lratPath_818_);
v_a_887_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_901_ == 0)
{
v___x_889_ = v___x_886_;
v_isShared_890_ = v_isSharedCheck_901_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_886_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_901_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v_ref_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
v_ref_891_ = lean_ctor_get(v_a_811_, 5);
v___x_892_ = lean_io_error_to_string(v_a_887_);
if (v_isShared_880_ == 0)
{
lean_ctor_set_tag(v___x_879_, 3);
lean_ctor_set(v___x_879_, 0, v___x_892_);
v___x_894_ = v___x_879_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_900_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_895_ = l_Lean_MessageData_ofFormat(v___x_894_);
lean_inc(v_ref_891_);
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v_ref_891_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_896_);
v___x_898_ = v___x_889_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_916_; 
lean_dec_ref(v_lratPath_818_);
v_a_902_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_916_ == 0)
{
v___x_904_ = v___x_884_;
v_isShared_905_ = v_isSharedCheck_916_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_884_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_916_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v_ref_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
v_ref_906_ = lean_ctor_get(v_a_811_, 5);
v___x_907_ = lean_io_error_to_string(v_a_902_);
if (v_isShared_880_ == 0)
{
lean_ctor_set_tag(v___x_879_, 3);
lean_ctor_set(v___x_879_, 0, v___x_907_);
v___x_909_ = v___x_879_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_915_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_910_ = l_Lean_MessageData_ofFormat(v___x_909_);
lean_inc(v_ref_906_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v_ref_906_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_911_);
v___x_913_ = v___x_904_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_931_; 
lean_dec_ref(v_lratPath_818_);
v_a_917_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_931_ == 0)
{
v___x_919_ = v___x_881_;
v_isShared_920_ = v_isSharedCheck_931_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_881_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_931_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v_ref_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
v_ref_921_ = lean_ctor_get(v_a_811_, 5);
v___x_922_ = lean_io_error_to_string(v_a_917_);
if (v_isShared_880_ == 0)
{
lean_ctor_set_tag(v___x_879_, 3);
lean_ctor_set(v___x_879_, 0, v___x_922_);
v___x_924_ = v___x_879_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_930_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_925_ = l_Lean_MessageData_ofFormat(v___x_924_);
lean_inc(v_ref_921_);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_ref_921_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v___x_926_);
v___x_928_ = v___x_919_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
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
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec_ref(v_lratPath_818_);
v_a_935_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_869_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_869_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___boxed(lean_object* v_target_947_, lean_object* v_ctx_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(v_target_947_, v_ctx_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0(lean_object* v_00_u03b1_960_, lean_object* v_msg_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(v_msg_961_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___boxed(lean_object* v_00_u03b1_973_, lean_object* v_msg_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0(v_00_u03b1_973_, v_msg_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
return v_res_985_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_986_ = lean_box(0);
v___x_987_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v___x_986_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg(){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0);
v___x_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___boxed(lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0(lean_object* v_00_u03b1_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___boxed(lean_object* v_00_u03b1_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0(v_00_u03b1_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(lean_object* v_snd_1016_, lean_object* v___y_1017_, lean_object* v_a_x3f_1018_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_io_remove_file(v_snd_1016_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1020_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1041_; 
v_a_1029_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1031_ = v___x_1020_;
v_isShared_1032_ = v_isSharedCheck_1041_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1020_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1041_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v_ref_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
v_ref_1033_ = lean_ctor_get(v___y_1017_, 5);
v___x_1034_ = lean_io_error_to_string(v_a_1029_);
v___x_1035_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
v___x_1036_ = l_Lean_MessageData_ofFormat(v___x_1035_);
lean_inc(v_ref_1033_);
v___x_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1037_, 0, v_ref_1033_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v___x_1037_);
v___x_1039_ = v___x_1031_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0___boxed(lean_object* v_snd_1042_, lean_object* v___y_1043_, lean_object* v_a_x3f_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_1042_, v___y_1043_, v_a_x3f_1044_);
lean_dec(v_a_x3f_1044_);
lean_dec_ref(v___y_1043_);
lean_dec_ref(v_snd_1042_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(lean_object* v_f_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v_fst_1059_; lean_object* v_snd_1060_; lean_object* v_r_1061_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
lean_dec_ref_known(v___x_1057_, 1);
v_fst_1059_ = lean_ctor_get(v_a_1058_, 0);
lean_inc(v_fst_1059_);
v_snd_1060_ = lean_ctor_get(v_a_1058_, 1);
lean_inc_n(v_snd_1060_, 2);
lean_dec(v_a_1058_);
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
lean_inc(v___y_1051_);
lean_inc_ref(v___y_1050_);
lean_inc(v___y_1049_);
lean_inc_ref(v___y_1048_);
v_r_1061_ = lean_apply_11(v_f_1047_, v_fst_1059_, v_snd_1060_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, lean_box(0));
if (lean_obj_tag(v_r_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1086_; 
v_a_1062_ = lean_ctor_get(v_r_1061_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_r_1061_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1064_ = v_r_1061_;
v_isShared_1065_ = v_isSharedCheck_1086_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v_r_1061_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1086_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
lean_inc(v_a_1062_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set_tag(v___x_1064_, 1);
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_1060_, v___y_1054_, v___x_1067_);
lean_dec_ref(v___x_1067_);
lean_dec(v_snd_1060_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; 
v_unused_1076_ = lean_ctor_get(v___x_1068_, 0);
lean_dec(v_unused_1076_);
v___x_1070_ = v___x_1068_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_dec(v___x_1068_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v_a_1062_);
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1062_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
lean_dec(v_a_1062_);
v_a_1077_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1068_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1068_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_a_1087_ = lean_ctor_get(v_r_1061_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v_r_1061_, 1);
v___x_1088_ = lean_box(0);
v___x_1089_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_1060_, v___y_1054_, v___x_1088_);
lean_dec(v_snd_1060_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; 
v_unused_1097_ = lean_ctor_get(v___x_1089_, 0);
lean_dec(v_unused_1097_);
v___x_1091_ = v___x_1089_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_dec(v___x_1089_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set_tag(v___x_1091_, 1);
lean_ctor_set(v___x_1091_, 0, v_a_1087_);
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1087_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec(v_a_1087_);
v_a_1098_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1089_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1089_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1118_; 
lean_dec_ref(v_f_1047_);
v_a_1106_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1108_ = v___x_1057_;
v_isShared_1109_ = v_isSharedCheck_1118_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1057_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1118_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v_ref_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1116_; 
v_ref_1110_ = lean_ctor_get(v___y_1054_, 5);
v___x_1111_ = lean_io_error_to_string(v_a_1106_);
v___x_1112_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
v___x_1113_ = l_Lean_MessageData_ofFormat(v___x_1112_);
lean_inc(v_ref_1110_);
v___x_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1114_, 0, v_ref_1110_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1114_);
v___x_1116_ = v___x_1108_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___boxed(lean_object* v_f_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(v_f_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1(lean_object* v_00_u03b1_1130_, lean_object* v_f_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(v_f_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___boxed(lean_object* v_00_u03b1_1142_, lean_object* v_f_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1(v_00_u03b1_1142_, v_f_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0(uint8_t v___x_1154_, uint8_t v___x_1155_, lean_object* v___x_1156_, lean_object* v___x_1157_, lean_object* v_a_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1160_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1169_);
lean_dec_ref_known(v___x_1168_, 1);
v___x_1170_ = lean_unsigned_to_nat(9u);
v___x_1171_ = lean_unsigned_to_nat(5u);
v___x_1172_ = lean_unsigned_to_nat(8u);
v___x_1173_ = lean_unsigned_to_nat(1000u);
v___x_1174_ = lean_unsigned_to_nat(1024u);
v___x_1175_ = lean_unsigned_to_nat(10000u);
v___x_1176_ = lean_unsigned_to_nat(1048576u);
v___x_1177_ = lean_unsigned_to_nat(50u);
v___x_1178_ = lean_box(0);
v___x_1179_ = lean_alloc_ctor(0, 14, 32);
lean_ctor_set(v___x_1179_, 0, v___x_1170_);
lean_ctor_set(v___x_1179_, 1, v___x_1171_);
lean_ctor_set(v___x_1179_, 2, v___x_1172_);
lean_ctor_set(v___x_1179_, 3, v___x_1172_);
lean_ctor_set(v___x_1179_, 4, v___x_1173_);
lean_ctor_set(v___x_1179_, 5, v___x_1173_);
lean_ctor_set(v___x_1179_, 6, v___x_1156_);
lean_ctor_set(v___x_1179_, 7, v___x_1174_);
lean_ctor_set(v___x_1179_, 8, v___x_1175_);
lean_ctor_set(v___x_1179_, 9, v___x_1173_);
lean_ctor_set(v___x_1179_, 10, v___x_1176_);
lean_ctor_set(v___x_1179_, 11, v___x_1157_);
lean_ctor_set(v___x_1179_, 12, v___x_1177_);
lean_ctor_set(v___x_1179_, 13, v___x_1178_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14, v___x_1154_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 1, v___x_1154_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 2, v___x_1154_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 3, v___x_1154_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 4, v___x_1154_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 5, v___x_1155_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 6, v___x_1155_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 7, v___x_1155_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 8, v___x_1154_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 9, v___x_1154_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 10, v___x_1155_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 11, v___x_1154_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 12, v___x_1155_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 13, v___x_1155_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 14, v___x_1155_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 15, v___x_1155_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 16, v___x_1155_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 17, v___x_1154_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 18, v___x_1155_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 19, v___x_1155_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 20, v___x_1155_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 21, v___x_1155_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 22, v___x_1155_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 23, v___x_1155_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 24, v___x_1155_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 25, v___x_1155_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 26, v___x_1155_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 27, v___x_1155_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 28, v___x_1155_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 29, v___x_1154_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 30, v___x_1155_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*14 + 31, v___x_1155_);
v___x_1180_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_1179_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1181_);
lean_dec_ref_known(v___x_1180_, 1);
v___x_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1182_, 0, v_a_1169_);
v___x_1183_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed), 12, 2);
lean_closure_set(v___x_1183_, 0, v___x_1182_);
lean_closure_set(v___x_1183_, 1, v_a_1158_);
v___x_1184_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___x_1183_, v_a_1181_, v___x_1178_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_dec_ref_known(v___x_1184_, 1);
v___x_1185_ = lean_box(0);
v___x_1186_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1185_, v___y_1160_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1194_; 
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1194_ == 0)
{
lean_object* v_unused_1195_; 
v_unused_1195_ = lean_ctor_get(v___x_1186_, 0);
lean_dec(v_unused_1195_);
v___x_1188_ = v___x_1186_;
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
else
{
lean_dec(v___x_1186_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1190_ = lean_box(0);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1190_);
v___x_1192_ = v___x_1188_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
else
{
return v___x_1186_;
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
v_a_1196_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1184_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1184_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1158_);
v_a_1204_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1180_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1180_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
lean_dec_ref(v_a_1158_);
lean_dec(v___x_1157_);
lean_dec(v___x_1156_);
v_a_1212_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1168_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1168_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0___boxed(lean_object* v___x_1220_, lean_object* v___x_1221_, lean_object* v___x_1222_, lean_object* v___x_1223_, lean_object* v_a_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
uint8_t v___x_6747__boxed_1234_; uint8_t v___x_6748__boxed_1235_; lean_object* v_res_1236_; 
v___x_6747__boxed_1234_ = lean_unbox(v___x_1220_);
v___x_6748__boxed_1235_ = lean_unbox(v___x_1221_);
v_res_1236_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0(v___x_6747__boxed_1234_, v___x_6748__boxed_1235_, v___x_1222_, v___x_1223_, v_a_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1(lean_object* v_a_1237_, lean_object* v_a_1238_, uint8_t v___x_1239_, uint8_t v___x_1240_, lean_object* v___x_1241_, lean_object* v___x_1242_, lean_object* v_x_1243_, lean_object* v_lratFile_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new(v_lratFile_1244_, v_a_1237_, v_a_1238_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___f_1258_; lean_object* v___x_1259_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref_known(v___x_1254_, 1);
v___x_1256_ = lean_box(v___x_1239_);
v___x_1257_ = lean_box(v___x_1240_);
v___f_1258_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0___boxed), 14, 5);
lean_closure_set(v___f_1258_, 0, v___x_1256_);
lean_closure_set(v___f_1258_, 1, v___x_1257_);
lean_closure_set(v___f_1258_, 2, v___x_1241_);
lean_closure_set(v___f_1258_, 3, v___x_1242_);
lean_closure_set(v___f_1258_, 4, v_a_1255_);
v___x_1259_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1258_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
return v___x_1259_;
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec(v___x_1242_);
lean_dec(v___x_1241_);
v_a_1260_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1254_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1254_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1___boxed(lean_object** _args){
lean_object* v_a_1268_ = _args[0];
lean_object* v_a_1269_ = _args[1];
lean_object* v___x_1270_ = _args[2];
lean_object* v___x_1271_ = _args[3];
lean_object* v___x_1272_ = _args[4];
lean_object* v___x_1273_ = _args[5];
lean_object* v_x_1274_ = _args[6];
lean_object* v_lratFile_1275_ = _args[7];
lean_object* v___y_1276_ = _args[8];
lean_object* v___y_1277_ = _args[9];
lean_object* v___y_1278_ = _args[10];
lean_object* v___y_1279_ = _args[11];
lean_object* v___y_1280_ = _args[12];
lean_object* v___y_1281_ = _args[13];
lean_object* v___y_1282_ = _args[14];
lean_object* v___y_1283_ = _args[15];
lean_object* v___y_1284_ = _args[16];
_start:
{
uint8_t v___x_6898__boxed_1285_; uint8_t v___x_6899__boxed_1286_; lean_object* v_res_1287_; 
v___x_6898__boxed_1285_ = lean_unbox(v___x_1270_);
v___x_6899__boxed_1286_ = lean_unbox(v___x_1271_);
v_res_1287_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1(v_a_1268_, v_a_1269_, v___x_6898__boxed_1285_, v___x_6899__boxed_1286_, v___x_1272_, v___x_1273_, v_x_1274_, v_lratFile_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v_x_1274_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide(lean_object* v_x_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1318_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3));
lean_inc(v_x_1308_);
v___x_1319_ = l_Lean_Syntax_isOfKind(v_x_1308_, v___x_1318_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; 
lean_dec(v_x_1308_);
v___x_1320_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1320_;
}
else
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; lean_object* v_types_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; 
v___x_1321_ = lean_unsigned_to_nat(1u);
v___x_1322_ = l_Lean_Syntax_getArg(v_x_1308_, v___x_1321_);
v___x_1323_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_1322_);
v___x_1324_ = l_Lean_Syntax_isOfKind(v___x_1322_, v___x_1323_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1365_; 
lean_dec(v___x_1322_);
lean_dec(v_x_1308_);
v___x_1365_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1365_;
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1366_ = lean_unsigned_to_nat(2u);
v___x_1367_ = l_Lean_Syntax_getArg(v_x_1308_, v___x_1366_);
lean_dec(v_x_1308_);
v___x_1368_ = l_Lean_Syntax_isNone(v___x_1367_);
if (v___x_1368_ == 0)
{
uint8_t v___x_1369_; 
lean_inc(v___x_1367_);
v___x_1369_ = l_Lean_Syntax_matchesNull(v___x_1367_, v___x_1321_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; 
lean_dec(v___x_1367_);
lean_dec(v___x_1322_);
v___x_1370_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1370_;
}
else
{
lean_object* v___x_1371_; lean_object* v_types_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1371_ = lean_unsigned_to_nat(0u);
v_types_1372_ = l_Lean_Syntax_getArg(v___x_1367_, v___x_1371_);
lean_dec(v___x_1367_);
v___x_1373_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_types_1372_);
v___x_1374_ = l_Lean_Syntax_isOfKind(v_types_1372_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; 
lean_dec(v_types_1372_);
lean_dec(v___x_1322_);
v___x_1375_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1375_;
}
else
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1376_, 0, v_types_1372_);
v_types_1326_ = v___x_1376_;
v___y_1327_ = v_a_1309_;
v___y_1328_ = v_a_1310_;
v___y_1329_ = v_a_1311_;
v___y_1330_ = v_a_1312_;
v___y_1331_ = v_a_1313_;
v___y_1332_ = v_a_1314_;
v___y_1333_ = v_a_1315_;
v___y_1334_ = v_a_1316_;
goto v___jp_1325_;
}
}
}
else
{
lean_object* v___x_1377_; 
lean_dec(v___x_1367_);
v___x_1377_ = lean_box(0);
v_types_1326_ = v___x_1377_;
v___y_1327_ = v_a_1309_;
v___y_1328_ = v_a_1310_;
v___y_1329_ = v_a_1311_;
v___y_1330_ = v_a_1312_;
v___y_1331_ = v_a_1313_;
v___y_1332_ = v_a_1314_;
v___y_1333_ = v_a_1315_;
v___y_1334_ = v_a_1316_;
goto v___jp_1325_;
}
}
v___jp_1325_:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v___x_1336_; uint8_t v___x_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_dec_ref_known(v___x_1335_, 1);
v___x_1336_ = lean_unsigned_to_nat(10u);
v___x_1337_ = 0;
v___x_1338_ = lean_unsigned_to_nat(100000u);
v___x_1339_ = 0;
v___x_1340_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_1340_, 0, v___x_1336_);
lean_ctor_set(v___x_1340_, 1, v___x_1338_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*2, v___x_1324_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*2 + 1, v___x_1324_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*2 + 2, v___x_1337_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*2 + 3, v___x_1324_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*2 + 4, v___x_1324_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*2 + 5, v___x_1324_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*2 + 6, v___x_1324_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*2 + 7, v___x_1324_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*2 + 8, v___x_1337_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*2 + 9, v___x_1337_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*2 + 10, v___x_1339_);
v___x_1341_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_1322_, v___x_1340_, v___x_1324_, v___y_1327_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1343_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1342_);
lean_dec_ref_known(v___x_1341_, 1);
v___x_1343_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_types_1326_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___f_1347_; lean_object* v___x_1348_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref_known(v___x_1343_, 1);
v___x_1345_ = lean_box(v___x_1337_);
v___x_1346_ = lean_box(v___x_1324_);
v___f_1347_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1___boxed), 17, 6);
lean_closure_set(v___f_1347_, 0, v_a_1342_);
lean_closure_set(v___f_1347_, 1, v_a_1344_);
lean_closure_set(v___f_1347_, 2, v___x_1345_);
lean_closure_set(v___f_1347_, 3, v___x_1346_);
lean_closure_set(v___f_1347_, 4, v___x_1338_);
lean_closure_set(v___f_1347_, 5, v___x_1336_);
v___x_1348_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(v___f_1347_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
return v___x_1348_;
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec(v_a_1342_);
v_a_1349_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1343_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1343_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec(v_types_1326_);
v_a_1357_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1341_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1341_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
else
{
lean_dec(v_types_1326_);
lean_dec(v___x_1322_);
return v___x_1335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___boxed(lean_object* v_x_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide(v_x_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_);
lean_dec(v_a_1386_);
lean_dec_ref(v_a_1385_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1(){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1398_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1399_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3));
v___x_1400_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2));
v___x_1401_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___boxed), 10, 0);
v___x_1402_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1398_, v___x_1399_, v___x_1400_, v___x_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___boxed(lean_object* v_a_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1();
return v_res_1404_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_Array_mkArray0(lean_box(0));
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0(lean_object* v___x_1417_, lean_object* v_a_1418_, uint8_t v___x_1419_, lean_object* v___x_1420_, lean_object* v___x_1421_, lean_object* v___x_1422_, lean_object* v___x_1423_, lean_object* v_tk_1424_, lean_object* v_typesStx_1425_, lean_object* v___x_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(v___x_1417_, v_a_1418_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___x_1437_, 1);
if (lean_obj_tag(v_a_1438_) == 0)
{
lean_object* v_ref_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___y_1449_; 
v_ref_1439_ = lean_ctor_get(v___y_1434_, 5);
v___x_1440_ = l_Lean_SourceInfo_fromRef(v_ref_1439_, v___x_1419_);
v___x_1441_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__1));
v___x_1442_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__2));
v___x_1443_ = l_Lean_Name_mkStr4(v___x_1420_, v___x_1421_, v___x_1422_, v___x_1442_);
v___x_1444_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3));
lean_inc(v___x_1440_);
v___x_1445_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1440_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
v___x_1446_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5));
v___x_1447_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6);
if (lean_obj_tag(v_typesStx_1425_) == 1)
{
lean_object* v_val_1461_; lean_object* v___x_1462_; 
v_val_1461_ = lean_ctor_get(v_typesStx_1425_, 0);
lean_inc(v_val_1461_);
lean_dec_ref_known(v_typesStx_1425_, 1);
v___x_1462_ = l_Array_mkArray1___redArg(v_val_1461_);
v___y_1449_ = v___x_1462_;
goto v___jp_1448_;
}
else
{
lean_object* v___x_1463_; 
lean_dec(v_typesStx_1425_);
v___x_1463_ = lean_mk_empty_array_with_capacity(v___x_1426_);
v___y_1449_ = v___x_1463_;
goto v___jp_1448_;
}
v___jp_1448_:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1450_ = l_Array_append___redArg(v___x_1447_, v___y_1449_);
lean_dec_ref(v___y_1449_);
lean_inc(v___x_1440_);
v___x_1451_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1440_);
lean_ctor_set(v___x_1451_, 1, v___x_1446_);
lean_ctor_set(v___x_1451_, 2, v___x_1450_);
v___x_1452_ = l_Lean_Syntax_node3(v___x_1440_, v___x_1443_, v___x_1445_, v___x_1423_, v___x_1451_);
v___x_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1441_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
v___x_1454_ = lean_box(0);
v___x_1455_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1453_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
lean_ctor_set(v___x_1455_, 2, v___x_1454_);
lean_ctor_set(v___x_1455_, 3, v___x_1454_);
lean_ctor_set(v___x_1455_, 4, v___x_1454_);
lean_ctor_set(v___x_1455_, 5, v___x_1454_);
lean_inc(v_ref_1439_);
v___x_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1456_, 0, v_ref_1439_);
v___x_1457_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__7));
v___x_1458_ = 4;
v___x_1459_ = l_Lean_MessageData_nil;
v___x_1460_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1424_, v___x_1455_, v___x_1456_, v___x_1457_, v___x_1454_, v___x_1458_, v___x_1459_, v___y_1434_, v___y_1435_);
return v___x_1460_;
}
}
else
{
lean_object* v_path_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1497_; 
v_path_1464_ = lean_ctor_get(v_a_1438_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_a_1438_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1466_ = v_a_1438_;
v_isShared_1467_ = v_isSharedCheck_1497_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_path_1464_);
lean_dec(v_a_1438_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1497_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v_ref_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___y_1478_; 
v_ref_1468_ = lean_ctor_get(v___y_1434_, 5);
v___x_1469_ = l_Lean_SourceInfo_fromRef(v_ref_1468_, v___x_1419_);
v___x_1470_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__1));
v___x_1471_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__8));
v___x_1472_ = l_Lean_Name_mkStr4(v___x_1420_, v___x_1421_, v___x_1422_, v___x_1471_);
v___x_1473_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__9));
lean_inc(v___x_1469_);
v___x_1474_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1469_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
v___x_1475_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5));
v___x_1476_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6);
if (lean_obj_tag(v_typesStx_1425_) == 1)
{
lean_object* v_val_1494_; lean_object* v___x_1495_; 
v_val_1494_ = lean_ctor_get(v_typesStx_1425_, 0);
lean_inc(v_val_1494_);
lean_dec_ref_known(v_typesStx_1425_, 1);
v___x_1495_ = l_Array_mkArray1___redArg(v_val_1494_);
v___y_1478_ = v___x_1495_;
goto v___jp_1477_;
}
else
{
lean_object* v___x_1496_; 
lean_dec(v_typesStx_1425_);
v___x_1496_ = lean_mk_empty_array_with_capacity(v___x_1426_);
v___y_1478_ = v___x_1496_;
goto v___jp_1477_;
}
v___jp_1477_:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1488_; 
v___x_1479_ = l_Array_append___redArg(v___x_1476_, v___y_1478_);
lean_dec_ref(v___y_1478_);
lean_inc(v___x_1469_);
v___x_1480_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1469_);
lean_ctor_set(v___x_1480_, 1, v___x_1475_);
lean_ctor_set(v___x_1480_, 2, v___x_1479_);
v___x_1481_ = lean_box(2);
v___x_1482_ = l_Lean_Syntax_mkStrLit(v_path_1464_, v___x_1481_);
v___x_1483_ = l_Lean_Syntax_node4(v___x_1469_, v___x_1472_, v___x_1474_, v___x_1423_, v___x_1480_, v___x_1482_);
v___x_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1470_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
v___x_1485_ = lean_box(0);
v___x_1486_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1484_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
lean_ctor_set(v___x_1486_, 2, v___x_1485_);
lean_ctor_set(v___x_1486_, 3, v___x_1485_);
lean_ctor_set(v___x_1486_, 4, v___x_1485_);
lean_ctor_set(v___x_1486_, 5, v___x_1485_);
lean_inc(v_ref_1468_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v_ref_1468_);
v___x_1488_ = v___x_1466_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_ref_1468_);
v___x_1488_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1489_; uint8_t v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1489_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__7));
v___x_1490_ = 4;
v___x_1491_ = l_Lean_MessageData_nil;
v___x_1492_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1424_, v___x_1486_, v___x_1488_, v___x_1489_, v___x_1485_, v___x_1490_, v___x_1491_, v___y_1434_, v___y_1435_);
return v___x_1492_;
}
}
}
}
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec(v_typesStx_1425_);
lean_dec(v_tk_1424_);
lean_dec(v___x_1423_);
lean_dec_ref(v___x_1422_);
lean_dec_ref(v___x_1421_);
lean_dec_ref(v___x_1420_);
v_a_1498_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1437_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1437_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___boxed(lean_object** _args){
lean_object* v___x_1506_ = _args[0];
lean_object* v_a_1507_ = _args[1];
lean_object* v___x_1508_ = _args[2];
lean_object* v___x_1509_ = _args[3];
lean_object* v___x_1510_ = _args[4];
lean_object* v___x_1511_ = _args[5];
lean_object* v___x_1512_ = _args[6];
lean_object* v_tk_1513_ = _args[7];
lean_object* v_typesStx_1514_ = _args[8];
lean_object* v___x_1515_ = _args[9];
lean_object* v___y_1516_ = _args[10];
lean_object* v___y_1517_ = _args[11];
lean_object* v___y_1518_ = _args[12];
lean_object* v___y_1519_ = _args[13];
lean_object* v___y_1520_ = _args[14];
lean_object* v___y_1521_ = _args[15];
lean_object* v___y_1522_ = _args[16];
lean_object* v___y_1523_ = _args[17];
lean_object* v___y_1524_ = _args[18];
lean_object* v___y_1525_ = _args[19];
_start:
{
uint8_t v___x_22051__boxed_1526_; lean_object* v_res_1527_; 
v___x_22051__boxed_1526_ = lean_unbox(v___x_1508_);
v_res_1527_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0(v___x_1506_, v_a_1507_, v___x_22051__boxed_1526_, v___x_1509_, v___x_1510_, v___x_1511_, v___x_1512_, v_tk_1513_, v_typesStx_1514_, v___x_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec(v___x_1515_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic(lean_object* v_x_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v___x_1544_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0));
v___x_1545_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1));
v___x_1546_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1));
v___x_1547_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__1));
lean_inc(v_x_1534_);
v___x_1548_ = l_Lean_Syntax_isOfKind(v_x_1534_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; 
lean_dec(v_x_1534_);
v___x_1549_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1549_;
}
else
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1550_ = lean_unsigned_to_nat(1u);
v___x_1551_ = l_Lean_Syntax_getArg(v_x_1534_, v___x_1550_);
v___x_1552_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_1551_);
v___x_1553_ = l_Lean_Syntax_isOfKind(v___x_1551_, v___x_1552_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; 
lean_dec(v___x_1551_);
lean_dec(v_x_1534_);
v___x_1554_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1554_;
}
else
{
lean_object* v___x_1555_; lean_object* v_tk_1556_; lean_object* v_typesStx_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___x_1644_; lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1555_ = lean_unsigned_to_nat(0u);
v_tk_1556_ = l_Lean_Syntax_getArg(v_x_1534_, v___x_1555_);
v___x_1644_ = lean_unsigned_to_nat(2u);
v___x_1645_ = l_Lean_Syntax_getArg(v_x_1534_, v___x_1644_);
lean_dec(v_x_1534_);
v___x_1646_ = l_Lean_Syntax_isNone(v___x_1645_);
if (v___x_1646_ == 0)
{
uint8_t v___x_1647_; 
lean_inc(v___x_1645_);
v___x_1647_ = l_Lean_Syntax_matchesNull(v___x_1645_, v___x_1550_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; 
lean_dec(v___x_1645_);
lean_dec(v_tk_1556_);
lean_dec(v___x_1551_);
v___x_1648_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1648_;
}
else
{
lean_object* v_typesStx_1649_; lean_object* v___x_1650_; uint8_t v___x_1651_; 
v_typesStx_1649_ = l_Lean_Syntax_getArg(v___x_1645_, v___x_1555_);
lean_dec(v___x_1645_);
v___x_1650_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_typesStx_1649_);
v___x_1651_ = l_Lean_Syntax_isOfKind(v_typesStx_1649_, v___x_1650_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; 
lean_dec(v_typesStx_1649_);
lean_dec(v_tk_1556_);
lean_dec(v___x_1551_);
v___x_1652_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1652_;
}
else
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1653_, 0, v_typesStx_1649_);
v_typesStx_1558_ = v___x_1653_;
v___y_1559_ = v_a_1535_;
v___y_1560_ = v_a_1536_;
v___y_1561_ = v_a_1537_;
v___y_1562_ = v_a_1538_;
v___y_1563_ = v_a_1539_;
v___y_1564_ = v_a_1540_;
v___y_1565_ = v_a_1541_;
v___y_1566_ = v_a_1542_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v___x_1654_; 
lean_dec(v___x_1645_);
v___x_1654_ = lean_box(0);
v_typesStx_1558_ = v___x_1654_;
v___y_1559_ = v_a_1535_;
v___y_1560_ = v_a_1536_;
v___y_1561_ = v_a_1537_;
v___y_1562_ = v_a_1538_;
v___y_1563_ = v_a_1539_;
v___y_1564_ = v_a_1540_;
v___y_1565_ = v_a_1541_;
v___y_1566_ = v_a_1542_;
goto v___jp_1557_;
}
v___jp_1557_:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1642_; 
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1642_ == 0)
{
lean_object* v_unused_1643_; 
v_unused_1643_ = lean_ctor_get(v___x_1567_, 0);
lean_dec(v_unused_1643_);
v___x_1569_ = v___x_1567_;
v_isShared_1570_ = v_isSharedCheck_1642_;
goto v_resetjp_1568_;
}
else
{
lean_dec(v___x_1567_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1642_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; uint8_t v___x_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1571_ = lean_unsigned_to_nat(10u);
v___x_1572_ = 0;
v___x_1573_ = lean_unsigned_to_nat(100000u);
v___x_1574_ = 0;
v___x_1575_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_1575_, 0, v___x_1571_);
lean_ctor_set(v___x_1575_, 1, v___x_1573_);
lean_ctor_set_uint8(v___x_1575_, sizeof(void*)*2, v___x_1553_);
lean_ctor_set_uint8(v___x_1575_, sizeof(void*)*2 + 1, v___x_1553_);
lean_ctor_set_uint8(v___x_1575_, sizeof(void*)*2 + 2, v___x_1572_);
lean_ctor_set_uint8(v___x_1575_, sizeof(void*)*2 + 3, v___x_1553_);
lean_ctor_set_uint8(v___x_1575_, sizeof(void*)*2 + 4, v___x_1553_);
lean_ctor_set_uint8(v___x_1575_, sizeof(void*)*2 + 5, v___x_1553_);
lean_ctor_set_uint8(v___x_1575_, sizeof(void*)*2 + 6, v___x_1553_);
lean_ctor_set_uint8(v___x_1575_, sizeof(void*)*2 + 7, v___x_1553_);
lean_ctor_set_uint8(v___x_1575_, sizeof(void*)*2 + 8, v___x_1572_);
lean_ctor_set_uint8(v___x_1575_, sizeof(void*)*2 + 9, v___x_1572_);
lean_ctor_set_uint8(v___x_1575_, sizeof(void*)*2 + 10, v___x_1574_);
lean_inc(v___x_1551_);
v___x_1576_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_1551_, v___x_1575_, v___x_1553_, v___y_1559_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1578_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1577_);
lean_dec_ref_known(v___x_1576_, 1);
lean_inc(v_typesStx_1558_);
v___x_1578_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_1558_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v___x_1580_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v___x_1578_, 1);
v___x_1580_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(v_a_1577_, v_a_1579_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1582_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v___x_1580_, 1);
v___x_1582_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1560_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v___x_1584_ = lean_unsigned_to_nat(9u);
v___x_1585_ = lean_unsigned_to_nat(5u);
v___x_1586_ = lean_unsigned_to_nat(8u);
v___x_1587_ = lean_unsigned_to_nat(1000u);
v___x_1588_ = lean_unsigned_to_nat(1024u);
v___x_1589_ = lean_unsigned_to_nat(10000u);
v___x_1590_ = lean_unsigned_to_nat(1048576u);
v___x_1591_ = lean_unsigned_to_nat(50u);
v___x_1592_ = lean_box(0);
v___x_1593_ = lean_alloc_ctor(0, 14, 32);
lean_ctor_set(v___x_1593_, 0, v___x_1584_);
lean_ctor_set(v___x_1593_, 1, v___x_1585_);
lean_ctor_set(v___x_1593_, 2, v___x_1586_);
lean_ctor_set(v___x_1593_, 3, v___x_1586_);
lean_ctor_set(v___x_1593_, 4, v___x_1587_);
lean_ctor_set(v___x_1593_, 5, v___x_1587_);
lean_ctor_set(v___x_1593_, 6, v___x_1573_);
lean_ctor_set(v___x_1593_, 7, v___x_1588_);
lean_ctor_set(v___x_1593_, 8, v___x_1589_);
lean_ctor_set(v___x_1593_, 9, v___x_1587_);
lean_ctor_set(v___x_1593_, 10, v___x_1590_);
lean_ctor_set(v___x_1593_, 11, v___x_1571_);
lean_ctor_set(v___x_1593_, 12, v___x_1591_);
lean_ctor_set(v___x_1593_, 13, v___x_1592_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14, v___x_1572_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 1, v___x_1572_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 2, v___x_1572_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 3, v___x_1572_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 4, v___x_1572_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 5, v___x_1553_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 6, v___x_1553_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 7, v___x_1553_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 8, v___x_1572_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 9, v___x_1572_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 10, v___x_1553_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 11, v___x_1572_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 12, v___x_1553_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 13, v___x_1553_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 14, v___x_1553_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 15, v___x_1553_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 16, v___x_1553_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 17, v___x_1572_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 18, v___x_1553_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 19, v___x_1553_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 20, v___x_1553_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 21, v___x_1553_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 22, v___x_1553_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 23, v___x_1553_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 24, v___x_1553_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 25, v___x_1553_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 26, v___x_1553_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 27, v___x_1553_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 28, v___x_1553_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 29, v___x_1572_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 30, v___x_1553_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 31, v___x_1553_);
v___x_1594_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_1593_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1597_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___x_1594_, 1);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v_a_1583_);
v___x_1597_ = v___x_1569_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1583_);
v___x_1597_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1598_; lean_object* v___f_1599_; lean_object* v___x_1600_; 
v___x_1598_ = lean_box(v___x_1572_);
v___f_1599_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___boxed), 20, 10);
lean_closure_set(v___f_1599_, 0, v___x_1597_);
lean_closure_set(v___f_1599_, 1, v_a_1581_);
lean_closure_set(v___f_1599_, 2, v___x_1598_);
lean_closure_set(v___f_1599_, 3, v___x_1544_);
lean_closure_set(v___f_1599_, 4, v___x_1545_);
lean_closure_set(v___f_1599_, 5, v___x_1546_);
lean_closure_set(v___f_1599_, 6, v___x_1551_);
lean_closure_set(v___f_1599_, 7, v_tk_1556_);
lean_closure_set(v___f_1599_, 8, v_typesStx_1558_);
lean_closure_set(v___f_1599_, 9, v___x_1555_);
v___x_1600_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___f_1599_, v_a_1595_, v___x_1592_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
return v___x_1600_;
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec(v_a_1583_);
lean_dec(v_a_1581_);
lean_del_object(v___x_1569_);
lean_dec(v_typesStx_1558_);
lean_dec(v_tk_1556_);
lean_dec(v___x_1551_);
v_a_1602_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1594_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1594_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_dec(v_a_1581_);
lean_del_object(v___x_1569_);
lean_dec(v_typesStx_1558_);
lean_dec(v_tk_1556_);
lean_dec(v___x_1551_);
v_a_1610_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1582_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1582_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_del_object(v___x_1569_);
lean_dec(v_typesStx_1558_);
lean_dec(v_tk_1556_);
lean_dec(v___x_1551_);
v_a_1618_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1580_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1580_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
lean_dec(v_a_1577_);
lean_del_object(v___x_1569_);
lean_dec(v_typesStx_1558_);
lean_dec(v_tk_1556_);
lean_dec(v___x_1551_);
v_a_1626_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1578_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1578_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
lean_del_object(v___x_1569_);
lean_dec(v_typesStx_1558_);
lean_dec(v_tk_1556_);
lean_dec(v___x_1551_);
v_a_1634_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1576_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1576_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
}
else
{
lean_dec(v_typesStx_1558_);
lean_dec(v_tk_1556_);
lean_dec(v___x_1551_);
return v___x_1567_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___boxed(lean_object* v_x_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic(v_x_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
lean_dec(v_a_1663_);
lean_dec_ref(v_a_1662_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
lean_dec(v_a_1659_);
lean_dec_ref(v_a_1658_);
lean_dec(v_a_1657_);
lean_dec_ref(v_a_1656_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1(){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1674_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1675_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__1));
v___x_1676_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___closed__1));
v___x_1677_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___boxed), 10, 0);
v___x_1678_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1674_, v___x_1675_, v___x_1676_, v___x_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___boxed(lean_object* v_a_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1();
return v_res_1680_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_1687_, uint8_t v_suppressElabErrors_1688_, lean_object* v_x_1689_){
_start:
{
if (lean_obj_tag(v_x_1689_) == 1)
{
lean_object* v_pre_1690_; 
v_pre_1690_ = lean_ctor_get(v_x_1689_, 0);
switch(lean_obj_tag(v_pre_1690_))
{
case 1:
{
lean_object* v_pre_1691_; 
v_pre_1691_ = lean_ctor_get(v_pre_1690_, 0);
switch(lean_obj_tag(v_pre_1691_))
{
case 0:
{
lean_object* v_str_1692_; lean_object* v_str_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
v_str_1692_ = lean_ctor_get(v_x_1689_, 1);
v_str_1693_ = lean_ctor_get(v_pre_1690_, 1);
v___x_1694_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__0));
v___x_1695_ = lean_string_dec_eq(v_str_1693_, v___x_1694_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; uint8_t v___x_1697_; 
v___x_1696_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1));
v___x_1697_ = lean_string_dec_eq(v_str_1693_, v___x_1696_);
if (v___x_1697_ == 0)
{
return v___y_1687_;
}
else
{
lean_object* v___x_1698_; uint8_t v___x_1699_; 
v___x_1698_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_1699_ = lean_string_dec_eq(v_str_1692_, v___x_1698_);
if (v___x_1699_ == 0)
{
return v___y_1687_;
}
else
{
return v_suppressElabErrors_1688_;
}
}
}
else
{
lean_object* v___x_1700_; uint8_t v___x_1701_; 
v___x_1700_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_1701_ = lean_string_dec_eq(v_str_1692_, v___x_1700_);
if (v___x_1701_ == 0)
{
return v___y_1687_;
}
else
{
return v_suppressElabErrors_1688_;
}
}
}
case 1:
{
lean_object* v_pre_1702_; 
v_pre_1702_ = lean_ctor_get(v_pre_1691_, 0);
if (lean_obj_tag(v_pre_1702_) == 0)
{
lean_object* v_str_1703_; lean_object* v_str_1704_; lean_object* v_str_1705_; lean_object* v___x_1706_; uint8_t v___x_1707_; 
v_str_1703_ = lean_ctor_get(v_x_1689_, 1);
v_str_1704_ = lean_ctor_get(v_pre_1690_, 1);
v_str_1705_ = lean_ctor_get(v_pre_1691_, 1);
v___x_1706_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_1707_ = lean_string_dec_eq(v_str_1705_, v___x_1706_);
if (v___x_1707_ == 0)
{
return v___y_1687_;
}
else
{
lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1708_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_1709_ = lean_string_dec_eq(v_str_1704_, v___x_1708_);
if (v___x_1709_ == 0)
{
return v___y_1687_;
}
else
{
lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1710_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_1711_ = lean_string_dec_eq(v_str_1703_, v___x_1710_);
if (v___x_1711_ == 0)
{
return v___y_1687_;
}
else
{
return v_suppressElabErrors_1688_;
}
}
}
}
else
{
return v___y_1687_;
}
}
default: 
{
return v___y_1687_;
}
}
}
case 0:
{
lean_object* v_str_1712_; lean_object* v___x_1713_; uint8_t v___x_1714_; 
v_str_1712_ = lean_ctor_get(v_x_1689_, 1);
v___x_1713_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_1714_ = lean_string_dec_eq(v_str_1712_, v___x_1713_);
if (v___x_1714_ == 0)
{
return v___y_1687_;
}
else
{
return v_suppressElabErrors_1688_;
}
}
default: 
{
return v___y_1687_;
}
}
}
else
{
return v___y_1687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_1715_, lean_object* v_suppressElabErrors_1716_, lean_object* v_x_1717_){
_start:
{
uint8_t v___y_8349__boxed_1718_; uint8_t v_suppressElabErrors_boxed_1719_; uint8_t v_res_1720_; lean_object* v_r_1721_; 
v___y_8349__boxed_1718_ = lean_unbox(v___y_1715_);
v_suppressElabErrors_boxed_1719_ = lean_unbox(v_suppressElabErrors_1716_);
v_res_1720_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0(v___y_8349__boxed_1718_, v_suppressElabErrors_boxed_1719_, v_x_1717_);
lean_dec(v_x_1717_);
v_r_1721_ = lean_box(v_res_1720_);
return v_r_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(lean_object* v_ref_1723_, lean_object* v_msgData_1724_, uint8_t v_severity_1725_, uint8_t v_isSilent_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
uint8_t v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; uint8_t v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1769_; uint8_t v___y_1770_; lean_object* v___y_1771_; uint8_t v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; uint8_t v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1794_; uint8_t v___y_1795_; lean_object* v___y_1796_; uint8_t v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; uint8_t v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1805_; lean_object* v___y_1806_; uint8_t v___y_1807_; lean_object* v___y_1808_; uint8_t v___y_1809_; lean_object* v___y_1810_; uint8_t v___y_1811_; uint8_t v___x_1816_; lean_object* v___y_1818_; lean_object* v___y_1819_; uint8_t v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; uint8_t v___y_1823_; uint8_t v___y_1824_; uint8_t v___y_1826_; uint8_t v___x_1841_; 
v___x_1816_ = 2;
v___x_1841_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1725_, v___x_1816_);
if (v___x_1841_ == 0)
{
v___y_1826_ = v___x_1841_;
goto v___jp_1825_;
}
else
{
uint8_t v___x_1842_; 
lean_inc_ref(v_msgData_1724_);
v___x_1842_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1724_);
v___y_1826_ = v___x_1842_;
goto v___jp_1825_;
}
v___jp_1732_:
{
lean_object* v___x_1742_; lean_object* v_currNamespace_1743_; lean_object* v_openDecls_1744_; lean_object* v_env_1745_; lean_object* v_nextMacroScope_1746_; lean_object* v_ngen_1747_; lean_object* v_auxDeclNGen_1748_; lean_object* v_traceState_1749_; lean_object* v_cache_1750_; lean_object* v_messages_1751_; lean_object* v_infoState_1752_; lean_object* v_snapshotTasks_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1767_; 
v___x_1742_ = lean_st_ref_take(v___y_1741_);
v_currNamespace_1743_ = lean_ctor_get(v___y_1740_, 6);
v_openDecls_1744_ = lean_ctor_get(v___y_1740_, 7);
v_env_1745_ = lean_ctor_get(v___x_1742_, 0);
v_nextMacroScope_1746_ = lean_ctor_get(v___x_1742_, 1);
v_ngen_1747_ = lean_ctor_get(v___x_1742_, 2);
v_auxDeclNGen_1748_ = lean_ctor_get(v___x_1742_, 3);
v_traceState_1749_ = lean_ctor_get(v___x_1742_, 4);
v_cache_1750_ = lean_ctor_get(v___x_1742_, 5);
v_messages_1751_ = lean_ctor_get(v___x_1742_, 6);
v_infoState_1752_ = lean_ctor_get(v___x_1742_, 7);
v_snapshotTasks_1753_ = lean_ctor_get(v___x_1742_, 8);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1755_ = v___x_1742_;
v_isShared_1756_ = v_isSharedCheck_1767_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_snapshotTasks_1753_);
lean_inc(v_infoState_1752_);
lean_inc(v_messages_1751_);
lean_inc(v_cache_1750_);
lean_inc(v_traceState_1749_);
lean_inc(v_auxDeclNGen_1748_);
lean_inc(v_ngen_1747_);
lean_inc(v_nextMacroScope_1746_);
lean_inc(v_env_1745_);
lean_dec(v___x_1742_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1767_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1762_; 
lean_inc(v_openDecls_1744_);
lean_inc(v_currNamespace_1743_);
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v_currNamespace_1743_);
lean_ctor_set(v___x_1757_, 1, v_openDecls_1744_);
v___x_1758_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
lean_ctor_set(v___x_1758_, 1, v___y_1736_);
lean_inc_ref(v___y_1735_);
lean_inc_ref(v___y_1737_);
v___x_1759_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1759_, 0, v___y_1737_);
lean_ctor_set(v___x_1759_, 1, v___y_1738_);
lean_ctor_set(v___x_1759_, 2, v___y_1734_);
lean_ctor_set(v___x_1759_, 3, v___y_1735_);
lean_ctor_set(v___x_1759_, 4, v___x_1758_);
lean_ctor_set_uint8(v___x_1759_, sizeof(void*)*5, v___y_1733_);
lean_ctor_set_uint8(v___x_1759_, sizeof(void*)*5 + 1, v___y_1739_);
lean_ctor_set_uint8(v___x_1759_, sizeof(void*)*5 + 2, v_isSilent_1726_);
v___x_1760_ = l_Lean_MessageLog_add(v___x_1759_, v_messages_1751_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 6, v___x_1760_);
v___x_1762_ = v___x_1755_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_env_1745_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v_nextMacroScope_1746_);
lean_ctor_set(v_reuseFailAlloc_1766_, 2, v_ngen_1747_);
lean_ctor_set(v_reuseFailAlloc_1766_, 3, v_auxDeclNGen_1748_);
lean_ctor_set(v_reuseFailAlloc_1766_, 4, v_traceState_1749_);
lean_ctor_set(v_reuseFailAlloc_1766_, 5, v_cache_1750_);
lean_ctor_set(v_reuseFailAlloc_1766_, 6, v___x_1760_);
lean_ctor_set(v_reuseFailAlloc_1766_, 7, v_infoState_1752_);
lean_ctor_set(v_reuseFailAlloc_1766_, 8, v_snapshotTasks_1753_);
v___x_1762_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1763_ = lean_st_ref_set(v___y_1741_, v___x_1762_);
v___x_1764_ = lean_box(0);
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
return v___x_1765_;
}
}
}
v___jp_1768_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1792_; 
v___x_1777_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1724_);
v___x_1778_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v___x_1777_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1781_ = v___x_1778_;
v_isShared_1782_ = v_isSharedCheck_1792_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1778_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1792_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
lean_inc_ref_n(v___y_1771_, 2);
v___x_1783_ = l_Lean_FileMap_toPosition(v___y_1771_, v___y_1774_);
lean_dec(v___y_1774_);
v___x_1784_ = l_Lean_FileMap_toPosition(v___y_1771_, v___y_1776_);
lean_dec(v___y_1776_);
v___x_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
v___x_1786_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___closed__0));
if (v___y_1772_ == 0)
{
lean_del_object(v___x_1781_);
lean_dec_ref(v___y_1769_);
v___y_1733_ = v___y_1770_;
v___y_1734_ = v___x_1785_;
v___y_1735_ = v___x_1786_;
v___y_1736_ = v_a_1779_;
v___y_1737_ = v___y_1773_;
v___y_1738_ = v___x_1783_;
v___y_1739_ = v___y_1775_;
v___y_1740_ = v___y_1729_;
v___y_1741_ = v___y_1730_;
goto v___jp_1732_;
}
else
{
uint8_t v___x_1787_; 
lean_inc(v_a_1779_);
v___x_1787_ = l_Lean_MessageData_hasTag(v___y_1769_, v_a_1779_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; lean_object* v___x_1790_; 
lean_dec_ref_known(v___x_1785_, 1);
lean_dec_ref(v___x_1783_);
lean_dec(v_a_1779_);
v___x_1788_ = lean_box(0);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1788_);
v___x_1790_ = v___x_1781_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
else
{
lean_del_object(v___x_1781_);
v___y_1733_ = v___y_1770_;
v___y_1734_ = v___x_1785_;
v___y_1735_ = v___x_1786_;
v___y_1736_ = v_a_1779_;
v___y_1737_ = v___y_1773_;
v___y_1738_ = v___x_1783_;
v___y_1739_ = v___y_1775_;
v___y_1740_ = v___y_1729_;
v___y_1741_ = v___y_1730_;
goto v___jp_1732_;
}
}
}
}
v___jp_1793_:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Lean_Syntax_getTailPos_x3f(v___y_1799_, v___y_1795_);
lean_dec(v___y_1799_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_inc(v___y_1801_);
v___y_1769_ = v___y_1794_;
v___y_1770_ = v___y_1795_;
v___y_1771_ = v___y_1796_;
v___y_1772_ = v___y_1797_;
v___y_1773_ = v___y_1798_;
v___y_1774_ = v___y_1801_;
v___y_1775_ = v___y_1800_;
v___y_1776_ = v___y_1801_;
goto v___jp_1768_;
}
else
{
lean_object* v_val_1803_; 
v_val_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_val_1803_);
lean_dec_ref_known(v___x_1802_, 1);
v___y_1769_ = v___y_1794_;
v___y_1770_ = v___y_1795_;
v___y_1771_ = v___y_1796_;
v___y_1772_ = v___y_1797_;
v___y_1773_ = v___y_1798_;
v___y_1774_ = v___y_1801_;
v___y_1775_ = v___y_1800_;
v___y_1776_ = v_val_1803_;
goto v___jp_1768_;
}
}
v___jp_1804_:
{
lean_object* v_ref_1812_; lean_object* v___x_1813_; 
v_ref_1812_ = l_Lean_replaceRef(v_ref_1723_, v___y_1806_);
v___x_1813_ = l_Lean_Syntax_getPos_x3f(v_ref_1812_, v___y_1807_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v___x_1814_; 
v___x_1814_ = lean_unsigned_to_nat(0u);
v___y_1794_ = v___y_1805_;
v___y_1795_ = v___y_1807_;
v___y_1796_ = v___y_1808_;
v___y_1797_ = v___y_1809_;
v___y_1798_ = v___y_1810_;
v___y_1799_ = v_ref_1812_;
v___y_1800_ = v___y_1811_;
v___y_1801_ = v___x_1814_;
goto v___jp_1793_;
}
else
{
lean_object* v_val_1815_; 
v_val_1815_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_val_1815_);
lean_dec_ref_known(v___x_1813_, 1);
v___y_1794_ = v___y_1805_;
v___y_1795_ = v___y_1807_;
v___y_1796_ = v___y_1808_;
v___y_1797_ = v___y_1809_;
v___y_1798_ = v___y_1810_;
v___y_1799_ = v_ref_1812_;
v___y_1800_ = v___y_1811_;
v___y_1801_ = v_val_1815_;
goto v___jp_1793_;
}
}
v___jp_1817_:
{
if (v___y_1824_ == 0)
{
v___y_1805_ = v___y_1822_;
v___y_1806_ = v___y_1818_;
v___y_1807_ = v___y_1823_;
v___y_1808_ = v___y_1819_;
v___y_1809_ = v___y_1820_;
v___y_1810_ = v___y_1821_;
v___y_1811_ = v_severity_1725_;
goto v___jp_1804_;
}
else
{
v___y_1805_ = v___y_1822_;
v___y_1806_ = v___y_1818_;
v___y_1807_ = v___y_1823_;
v___y_1808_ = v___y_1819_;
v___y_1809_ = v___y_1820_;
v___y_1810_ = v___y_1821_;
v___y_1811_ = v___x_1816_;
goto v___jp_1804_;
}
}
v___jp_1825_:
{
if (v___y_1826_ == 0)
{
lean_object* v_fileName_1827_; lean_object* v_fileMap_1828_; lean_object* v_options_1829_; lean_object* v_ref_1830_; uint8_t v_suppressElabErrors_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___f_1834_; uint8_t v___x_1835_; uint8_t v___x_1836_; 
v_fileName_1827_ = lean_ctor_get(v___y_1729_, 0);
v_fileMap_1828_ = lean_ctor_get(v___y_1729_, 1);
v_options_1829_ = lean_ctor_get(v___y_1729_, 2);
v_ref_1830_ = lean_ctor_get(v___y_1729_, 5);
v_suppressElabErrors_1831_ = lean_ctor_get_uint8(v___y_1729_, sizeof(void*)*14 + 1);
v___x_1832_ = lean_box(v___y_1826_);
v___x_1833_ = lean_box(v_suppressElabErrors_1831_);
v___f_1834_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1834_, 0, v___x_1832_);
lean_closure_set(v___f_1834_, 1, v___x_1833_);
v___x_1835_ = 1;
v___x_1836_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1725_, v___x_1835_);
if (v___x_1836_ == 0)
{
v___y_1818_ = v_ref_1830_;
v___y_1819_ = v_fileMap_1828_;
v___y_1820_ = v_suppressElabErrors_1831_;
v___y_1821_ = v_fileName_1827_;
v___y_1822_ = v___f_1834_;
v___y_1823_ = v___y_1826_;
v___y_1824_ = v___x_1836_;
goto v___jp_1817_;
}
else
{
lean_object* v___x_1837_; uint8_t v___x_1838_; 
v___x_1837_ = l_Lean_warningAsError;
v___x_1838_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_1829_, v___x_1837_);
v___y_1818_ = v_ref_1830_;
v___y_1819_ = v_fileMap_1828_;
v___y_1820_ = v_suppressElabErrors_1831_;
v___y_1821_ = v_fileName_1827_;
v___y_1822_ = v___f_1834_;
v___y_1823_ = v___y_1826_;
v___y_1824_ = v___x_1838_;
goto v___jp_1817_;
}
}
else
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
lean_dec_ref(v_msgData_1724_);
v___x_1839_ = lean_box(0);
v___x_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1839_);
return v___x_1840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_1843_, lean_object* v_msgData_1844_, lean_object* v_severity_1845_, lean_object* v_isSilent_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
uint8_t v_severity_boxed_1852_; uint8_t v_isSilent_boxed_1853_; lean_object* v_res_1854_; 
v_severity_boxed_1852_ = lean_unbox(v_severity_1845_);
v_isSilent_boxed_1853_ = lean_unbox(v_isSilent_1846_);
v_res_1854_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(v_ref_1843_, v_msgData_1844_, v_severity_boxed_1852_, v_isSilent_boxed_1853_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v_ref_1843_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(lean_object* v_msgData_1855_, uint8_t v_severity_1856_, uint8_t v_isSilent_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v_ref_1863_; lean_object* v___x_1864_; 
v_ref_1863_ = lean_ctor_get(v___y_1860_, 5);
v___x_1864_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(v_ref_1863_, v_msgData_1855_, v_severity_1856_, v_isSilent_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0___boxed(lean_object* v_msgData_1865_, lean_object* v_severity_1866_, lean_object* v_isSilent_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
uint8_t v_severity_boxed_1873_; uint8_t v_isSilent_boxed_1874_; lean_object* v_res_1875_; 
v_severity_boxed_1873_ = lean_unbox(v_severity_1866_);
v_isSilent_boxed_1874_ = lean_unbox(v_isSilent_1867_);
v_res_1875_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(v_msgData_1865_, v_severity_boxed_1873_, v_isSilent_boxed_1874_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(lean_object* v_msgData_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
uint8_t v___x_1882_; uint8_t v___x_1883_; lean_object* v___x_1884_; 
v___x_1882_ = 1;
v___x_1883_ = 0;
v___x_1884_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(v_msgData_1876_, v___x_1882_, v___x_1883_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0___boxed(lean_object* v_msgData_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(v_msgData_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
return v_res_1891_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__0));
v___x_1894_ = l_Lean_stringToMessageData(v___x_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0(uint8_t v___x_1895_, lean_object* v___x_1896_, lean_object* v___x_1897_, lean_object* v___x_1898_, lean_object* v___x_1899_, lean_object* v_tk_1900_, lean_object* v_typesStx_1901_, lean_object* v___x_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_ref_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___y_1918_; 
v_ref_1908_ = lean_ctor_get(v___y_1905_, 5);
v___x_1909_ = l_Lean_SourceInfo_fromRef(v_ref_1908_, v___x_1895_);
v___x_1910_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__1));
v___x_1911_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__2));
v___x_1912_ = l_Lean_Name_mkStr4(v___x_1896_, v___x_1897_, v___x_1898_, v___x_1911_);
v___x_1913_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3));
lean_inc(v___x_1909_);
v___x_1914_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1909_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5));
v___x_1916_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6);
if (lean_obj_tag(v_typesStx_1901_) == 1)
{
lean_object* v_val_1939_; lean_object* v___x_1940_; 
v_val_1939_ = lean_ctor_get(v_typesStx_1901_, 0);
lean_inc(v_val_1939_);
lean_dec_ref_known(v_typesStx_1901_, 1);
v___x_1940_ = l_Array_mkArray1___redArg(v_val_1939_);
v___y_1918_ = v___x_1940_;
goto v___jp_1917_;
}
else
{
lean_object* v___x_1941_; 
lean_dec(v_typesStx_1901_);
v___x_1941_ = lean_mk_empty_array_with_capacity(v___x_1902_);
v___y_1918_ = v___x_1941_;
goto v___jp_1917_;
}
v___jp_1917_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1, &l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1);
v___x_1920_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(v___x_1919_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1937_; 
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1937_ == 0)
{
lean_object* v_unused_1938_; 
v_unused_1938_ = lean_ctor_get(v___x_1920_, 0);
lean_dec(v_unused_1938_);
v___x_1922_ = v___x_1920_;
v_isShared_1923_ = v_isSharedCheck_1937_;
goto v_resetjp_1921_;
}
else
{
lean_dec(v___x_1920_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1937_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1924_ = l_Array_append___redArg(v___x_1916_, v___y_1918_);
lean_dec_ref(v___y_1918_);
lean_inc(v___x_1909_);
v___x_1925_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1909_);
lean_ctor_set(v___x_1925_, 1, v___x_1915_);
lean_ctor_set(v___x_1925_, 2, v___x_1924_);
v___x_1926_ = l_Lean_Syntax_node3(v___x_1909_, v___x_1912_, v___x_1914_, v___x_1899_, v___x_1925_);
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1910_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = lean_box(0);
v___x_1929_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1927_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
lean_ctor_set(v___x_1929_, 2, v___x_1928_);
lean_ctor_set(v___x_1929_, 3, v___x_1928_);
lean_ctor_set(v___x_1929_, 4, v___x_1928_);
lean_ctor_set(v___x_1929_, 5, v___x_1928_);
lean_inc(v_ref_1908_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set_tag(v___x_1922_, 1);
lean_ctor_set(v___x_1922_, 0, v_ref_1908_);
v___x_1931_ = v___x_1922_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_ref_1908_);
v___x_1931_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
lean_object* v___x_1932_; uint8_t v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1932_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__7));
v___x_1933_ = 4;
v___x_1934_ = l_Lean_MessageData_nil;
v___x_1935_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1900_, v___x_1929_, v___x_1931_, v___x_1932_, v___x_1928_, v___x_1933_, v___x_1934_, v___y_1905_, v___y_1906_);
return v___x_1935_;
}
}
}
else
{
lean_dec_ref(v___y_1918_);
lean_dec_ref_known(v___x_1914_, 2);
lean_dec(v___x_1912_);
lean_dec(v___x_1909_);
lean_dec(v_tk_1900_);
lean_dec(v___x_1899_);
return v___x_1920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___boxed(lean_object* v___x_1942_, lean_object* v___x_1943_, lean_object* v___x_1944_, lean_object* v___x_1945_, lean_object* v___x_1946_, lean_object* v_tk_1947_, lean_object* v_typesStx_1948_, lean_object* v___x_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
uint8_t v___x_8680__boxed_1955_; lean_object* v_res_1956_; 
v___x_8680__boxed_1955_ = lean_unbox(v___x_1942_);
v_res_1956_ = l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0(v___x_8680__boxed_1955_, v___x_1943_, v___x_1944_, v___x_1945_, v___x_1946_, v_tk_1947_, v_typesStx_1948_, v___x_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___x_1949_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic(lean_object* v_x_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; 
v___x_1975_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0));
v___x_1976_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1));
v___x_1977_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1));
v___x_1978_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0));
lean_inc(v_x_1965_);
v___x_1979_ = l_Lean_Syntax_isOfKind(v_x_1965_, v___x_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; 
lean_dec(v_x_1965_);
v___x_1980_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1980_;
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; 
v___x_1981_ = lean_unsigned_to_nat(1u);
v___x_1982_ = l_Lean_Syntax_getArg(v_x_1965_, v___x_1981_);
v___x_1983_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_1982_);
v___x_1984_ = l_Lean_Syntax_isOfKind(v___x_1982_, v___x_1983_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; 
lean_dec(v___x_1982_);
lean_dec(v_x_1965_);
v___x_1985_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1985_;
}
else
{
lean_object* v___x_1986_; lean_object* v_tk_1987_; lean_object* v_typesStx_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___x_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_1986_ = lean_unsigned_to_nat(0u);
v_tk_1987_ = l_Lean_Syntax_getArg(v_x_1965_, v___x_1986_);
v___x_2082_ = lean_unsigned_to_nat(2u);
v___x_2083_ = l_Lean_Syntax_getArg(v_x_1965_, v___x_2082_);
v___x_2084_ = l_Lean_Syntax_isNone(v___x_2083_);
if (v___x_2084_ == 0)
{
uint8_t v___x_2085_; 
lean_inc(v___x_2083_);
v___x_2085_ = l_Lean_Syntax_matchesNull(v___x_2083_, v___x_1981_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; 
lean_dec(v___x_2083_);
lean_dec(v_tk_1987_);
lean_dec(v___x_1982_);
lean_dec(v_x_1965_);
v___x_2086_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2086_;
}
else
{
lean_object* v_typesStx_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v_typesStx_2087_ = l_Lean_Syntax_getArg(v___x_2083_, v___x_1986_);
lean_dec(v___x_2083_);
v___x_2088_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_typesStx_2087_);
v___x_2089_ = l_Lean_Syntax_isOfKind(v_typesStx_2087_, v___x_2088_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; 
lean_dec(v_typesStx_2087_);
lean_dec(v_tk_1987_);
lean_dec(v___x_1982_);
lean_dec(v_x_1965_);
v___x_2090_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2090_;
}
else
{
lean_object* v___x_2091_; 
v___x_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2091_, 0, v_typesStx_2087_);
v_typesStx_1989_ = v___x_2091_;
v___y_1990_ = v_a_1966_;
v___y_1991_ = v_a_1967_;
v___y_1992_ = v_a_1968_;
v___y_1993_ = v_a_1969_;
v___y_1994_ = v_a_1970_;
v___y_1995_ = v_a_1971_;
v___y_1996_ = v_a_1972_;
v___y_1997_ = v_a_1973_;
goto v___jp_1988_;
}
}
}
else
{
lean_object* v___x_2092_; 
lean_dec(v___x_2083_);
v___x_2092_ = lean_box(0);
v_typesStx_1989_ = v___x_2092_;
v___y_1990_ = v_a_1966_;
v___y_1991_ = v_a_1967_;
v___y_1992_ = v_a_1968_;
v___y_1993_ = v_a_1969_;
v___y_1994_ = v_a_1970_;
v___y_1995_ = v_a_1971_;
v___y_1996_ = v_a_1972_;
v___y_1997_ = v_a_1973_;
goto v___jp_1988_;
}
v___jp_1988_:
{
lean_object* v___x_1998_; lean_object* v_path_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v___x_1998_ = lean_unsigned_to_nat(3u);
v_path_1999_ = l_Lean_Syntax_getArg(v_x_1965_, v___x_1998_);
lean_dec(v_x_1965_);
v___x_2000_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__2));
lean_inc(v_path_1999_);
v___x_2001_ = l_Lean_Syntax_isOfKind(v_path_1999_, v___x_2000_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2002_; 
lean_dec(v_path_1999_);
lean_dec(v_typesStx_1989_);
lean_dec(v_tk_1987_);
lean_dec(v___x_1982_);
v___x_2002_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2002_;
}
else
{
lean_object* v___x_2003_; 
v___x_2003_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2080_; 
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2080_ == 0)
{
lean_object* v_unused_2081_; 
v_unused_2081_ = lean_ctor_get(v___x_2003_, 0);
lean_dec(v_unused_2081_);
v___x_2005_ = v___x_2003_;
v_isShared_2006_ = v_isSharedCheck_2080_;
goto v_resetjp_2004_;
}
else
{
lean_dec(v___x_2003_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2080_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2007_; uint8_t v___x_2008_; lean_object* v___x_2009_; uint8_t v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2007_ = lean_unsigned_to_nat(10u);
v___x_2008_ = 0;
v___x_2009_ = lean_unsigned_to_nat(100000u);
v___x_2010_ = 0;
v___x_2011_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_2011_, 0, v___x_2007_);
lean_ctor_set(v___x_2011_, 1, v___x_2009_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*2, v___x_1984_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*2 + 1, v___x_1984_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*2 + 2, v___x_2008_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*2 + 3, v___x_1984_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*2 + 4, v___x_1984_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*2 + 5, v___x_1984_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*2 + 6, v___x_1984_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*2 + 7, v___x_1984_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*2 + 8, v___x_2008_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*2 + 9, v___x_2008_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*2 + 10, v___x_2010_);
lean_inc(v___x_1982_);
v___x_2012_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_1982_, v___x_2011_, v___x_1984_, v___y_1990_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2014_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref_known(v___x_2012_, 1);
lean_inc(v_typesStx_1989_);
v___x_2014_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_1989_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2014_, 1);
v___x_2016_ = l_Lean_TSyntax_getString(v_path_1999_);
lean_dec(v_path_1999_);
v___x_2017_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v___x_2016_, v_a_2013_, v_a_2015_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2019_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2018_);
lean_dec_ref_known(v___x_2017_, 1);
v___x_2019_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1991_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2019_, 1);
v___x_2021_ = lean_unsigned_to_nat(9u);
v___x_2022_ = lean_unsigned_to_nat(5u);
v___x_2023_ = lean_unsigned_to_nat(8u);
v___x_2024_ = lean_unsigned_to_nat(1000u);
v___x_2025_ = lean_unsigned_to_nat(1024u);
v___x_2026_ = lean_unsigned_to_nat(10000u);
v___x_2027_ = lean_unsigned_to_nat(1048576u);
v___x_2028_ = lean_unsigned_to_nat(50u);
v___x_2029_ = lean_box(0);
v___x_2030_ = lean_alloc_ctor(0, 14, 32);
lean_ctor_set(v___x_2030_, 0, v___x_2021_);
lean_ctor_set(v___x_2030_, 1, v___x_2022_);
lean_ctor_set(v___x_2030_, 2, v___x_2023_);
lean_ctor_set(v___x_2030_, 3, v___x_2023_);
lean_ctor_set(v___x_2030_, 4, v___x_2024_);
lean_ctor_set(v___x_2030_, 5, v___x_2024_);
lean_ctor_set(v___x_2030_, 6, v___x_2009_);
lean_ctor_set(v___x_2030_, 7, v___x_2025_);
lean_ctor_set(v___x_2030_, 8, v___x_2026_);
lean_ctor_set(v___x_2030_, 9, v___x_2024_);
lean_ctor_set(v___x_2030_, 10, v___x_2027_);
lean_ctor_set(v___x_2030_, 11, v___x_2007_);
lean_ctor_set(v___x_2030_, 12, v___x_2028_);
lean_ctor_set(v___x_2030_, 13, v___x_2029_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14, v___x_2008_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 1, v___x_2008_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 2, v___x_2008_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 3, v___x_2008_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 4, v___x_2008_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 5, v___x_1984_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 6, v___x_1984_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 7, v___x_1984_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 8, v___x_2008_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 9, v___x_2008_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 10, v___x_1984_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 11, v___x_2008_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 12, v___x_1984_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 13, v___x_1984_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 14, v___x_1984_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 15, v___x_1984_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 16, v___x_1984_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 17, v___x_2008_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 18, v___x_1984_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 19, v___x_1984_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 20, v___x_1984_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 21, v___x_1984_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 22, v___x_1984_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 23, v___x_1984_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 24, v___x_1984_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 25, v___x_1984_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 26, v___x_1984_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 27, v___x_1984_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 28, v___x_1984_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 29, v___x_2008_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 30, v___x_1984_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*14 + 31, v___x_1984_);
v___x_2031_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_2030_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2033_; lean_object* v___f_2034_; lean_object* v___x_2036_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2032_);
lean_dec_ref_known(v___x_2031_, 1);
v___x_2033_ = lean_box(v___x_2008_);
v___f_2034_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___boxed), 13, 8);
lean_closure_set(v___f_2034_, 0, v___x_2033_);
lean_closure_set(v___f_2034_, 1, v___x_1975_);
lean_closure_set(v___f_2034_, 2, v___x_1976_);
lean_closure_set(v___f_2034_, 3, v___x_1977_);
lean_closure_set(v___f_2034_, 4, v___x_1982_);
lean_closure_set(v___f_2034_, 5, v_tk_1987_);
lean_closure_set(v___f_2034_, 6, v_typesStx_1989_);
lean_closure_set(v___f_2034_, 7, v___x_1986_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v_a_2020_);
v___x_2036_ = v___x_2005_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2020_);
v___x_2036_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed), 13, 3);
lean_closure_set(v___x_2037_, 0, v___x_2036_);
lean_closure_set(v___x_2037_, 1, v_a_2018_);
lean_closure_set(v___x_2037_, 2, v___f_2034_);
v___x_2038_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___x_2037_, v_a_2032_, v___x_2029_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
return v___x_2038_;
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec(v_a_2020_);
lean_dec(v_a_2018_);
lean_del_object(v___x_2005_);
lean_dec(v_typesStx_1989_);
lean_dec(v_tk_1987_);
lean_dec(v___x_1982_);
v_a_2040_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2031_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2031_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec(v_a_2018_);
lean_del_object(v___x_2005_);
lean_dec(v_typesStx_1989_);
lean_dec(v_tk_1987_);
lean_dec(v___x_1982_);
v_a_2048_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_2019_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2019_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_del_object(v___x_2005_);
lean_dec(v_typesStx_1989_);
lean_dec(v_tk_1987_);
lean_dec(v___x_1982_);
v_a_2056_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2017_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2017_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec(v_a_2013_);
lean_del_object(v___x_2005_);
lean_dec(v_path_1999_);
lean_dec(v_typesStx_1989_);
lean_dec(v_tk_1987_);
lean_dec(v___x_1982_);
v_a_2064_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2014_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2014_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_del_object(v___x_2005_);
lean_dec(v_path_1999_);
lean_dec(v_typesStx_1989_);
lean_dec(v_tk_1987_);
lean_dec(v___x_1982_);
v_a_2072_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2012_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2012_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
}
else
{
lean_dec(v_path_1999_);
lean_dec(v_typesStx_1989_);
lean_dec(v_tk_1987_);
lean_dec(v___x_1982_);
return v___x_2003_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___boxed(lean_object* v_x_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic(v_x_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
lean_dec(v_a_2101_);
lean_dec_ref(v_a_2100_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
lean_dec(v_a_2097_);
lean_dec_ref(v_a_2096_);
lean_dec(v_a_2095_);
lean_dec_ref(v_a_2094_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1(){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2112_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2113_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0));
v___x_2114_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___closed__1));
v___x_2115_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___boxed), 10, 0);
v___x_2116_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2112_, v___x_2113_, v___x_2114_, v___x_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___boxed(lean_object* v_a_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1();
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0(lean_object* v___x_2119_, uint8_t v___x_2120_, lean_object* v___x_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2132_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1);
v___x_2133_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4);
v___x_2134_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5));
v___x_2135_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2135_, 0, v___x_2132_);
lean_ctor_set(v___x_2135_, 1, v___x_2132_);
lean_ctor_set(v___x_2135_, 2, v___x_2132_);
lean_ctor_set(v___x_2135_, 3, v___x_2133_);
lean_ctor_set(v___x_2135_, 4, v___x_2119_);
lean_ctor_set(v___x_2135_, 5, v___x_2134_);
lean_ctor_set_uint8(v___x_2135_, sizeof(void*)*6, v___x_2120_);
v___x_2136_ = lean_st_mk_ref(v___x_2135_);
v___x_2137_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_2121_, v___x_2136_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2147_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2140_ = v___x_2137_;
v_isShared_2141_ = v_isSharedCheck_2147_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2137_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2147_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2145_; 
v___x_2142_ = lean_st_ref_get(v___x_2136_);
lean_dec(v___x_2136_);
v___x_2143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2143_, 0, v_a_2138_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2143_);
v___x_2145_ = v___x_2140_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2143_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec(v___x_2136_);
v_a_2148_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2137_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2137_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0___boxed(lean_object* v___x_2156_, lean_object* v___x_2157_, lean_object* v___x_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
uint8_t v___x_4582__boxed_2169_; lean_object* v_res_2170_; 
v___x_4582__boxed_2169_ = lean_unbox(v___x_2157_);
v_res_2170_ = l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0(v___x_2156_, v___x_4582__boxed_2169_, v___x_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___x_2158_);
return v_res_2170_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_2171_, lean_object* v_i_2172_, lean_object* v_k_2173_){
_start:
{
lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2174_ = lean_array_get_size(v_keys_2171_);
v___x_2175_ = lean_nat_dec_lt(v_i_2172_, v___x_2174_);
if (v___x_2175_ == 0)
{
lean_dec(v_i_2172_);
return v___x_2175_;
}
else
{
lean_object* v_k_x27_2176_; uint8_t v___x_2177_; 
v_k_x27_2176_ = lean_array_fget_borrowed(v_keys_2171_, v_i_2172_);
v___x_2177_ = l_Lean_instBEqMVarId_beq(v_k_2173_, v_k_x27_2176_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = lean_unsigned_to_nat(1u);
v___x_2179_ = lean_nat_add(v_i_2172_, v___x_2178_);
lean_dec(v_i_2172_);
v_i_2172_ = v___x_2179_;
goto _start;
}
else
{
lean_dec(v_i_2172_);
return v___x_2177_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_2181_, lean_object* v_i_2182_, lean_object* v_k_2183_){
_start:
{
uint8_t v_res_2184_; lean_object* v_r_2185_; 
v_res_2184_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2181_, v_i_2182_, v_k_2183_);
lean_dec(v_k_2183_);
lean_dec_ref(v_keys_2181_);
v_r_2185_ = lean_box(v_res_2184_);
return v_r_2185_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2186_, size_t v_x_2187_, lean_object* v_x_2188_){
_start:
{
if (lean_obj_tag(v_x_2186_) == 0)
{
lean_object* v_es_2189_; lean_object* v___x_2190_; size_t v___x_2191_; size_t v___x_2192_; lean_object* v_j_2193_; lean_object* v___x_2194_; 
v_es_2189_ = lean_ctor_get(v_x_2186_, 0);
v___x_2190_ = lean_box(2);
v___x_2191_ = ((size_t)31ULL);
v___x_2192_ = lean_usize_land(v_x_2187_, v___x_2191_);
v_j_2193_ = lean_usize_to_nat(v___x_2192_);
v___x_2194_ = lean_array_get_borrowed(v___x_2190_, v_es_2189_, v_j_2193_);
lean_dec(v_j_2193_);
switch(lean_obj_tag(v___x_2194_))
{
case 0:
{
lean_object* v_key_2195_; uint8_t v___x_2196_; 
v_key_2195_ = lean_ctor_get(v___x_2194_, 0);
v___x_2196_ = l_Lean_instBEqMVarId_beq(v_x_2188_, v_key_2195_);
return v___x_2196_;
}
case 1:
{
lean_object* v_node_2197_; size_t v___x_2198_; size_t v___x_2199_; 
v_node_2197_ = lean_ctor_get(v___x_2194_, 0);
v___x_2198_ = ((size_t)5ULL);
v___x_2199_ = lean_usize_shift_right(v_x_2187_, v___x_2198_);
v_x_2186_ = v_node_2197_;
v_x_2187_ = v___x_2199_;
goto _start;
}
default: 
{
uint8_t v___x_2201_; 
v___x_2201_ = 0;
return v___x_2201_;
}
}
}
else
{
lean_object* v_ks_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v_ks_2202_ = lean_ctor_get(v_x_2186_, 0);
v___x_2203_ = lean_unsigned_to_nat(0u);
v___x_2204_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_2202_, v___x_2203_, v_x_2188_);
return v___x_2204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2205_, lean_object* v_x_2206_, lean_object* v_x_2207_){
_start:
{
size_t v_x_4687__boxed_2208_; uint8_t v_res_2209_; lean_object* v_r_2210_; 
v_x_4687__boxed_2208_ = lean_unbox_usize(v_x_2206_);
lean_dec(v_x_2206_);
v_res_2209_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_2205_, v_x_4687__boxed_2208_, v_x_2207_);
lean_dec(v_x_2207_);
lean_dec_ref(v_x_2205_);
v_r_2210_ = lean_box(v_res_2209_);
return v_r_2210_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(lean_object* v_x_2211_, lean_object* v_x_2212_){
_start:
{
uint64_t v___x_2213_; size_t v___x_2214_; uint8_t v___x_2215_; 
v___x_2213_ = l_Lean_instHashableMVarId_hash(v_x_2212_);
v___x_2214_ = lean_uint64_to_usize(v___x_2213_);
v___x_2215_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_2211_, v___x_2214_, v_x_2212_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_2216_, lean_object* v_x_2217_){
_start:
{
uint8_t v_res_2218_; lean_object* v_r_2219_; 
v_res_2218_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(v_x_2216_, v_x_2217_);
lean_dec(v_x_2217_);
lean_dec_ref(v_x_2216_);
v_r_2219_ = lean_box(v_res_2218_);
return v_r_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(lean_object* v_mvarId_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v___x_2223_; lean_object* v_mctx_2224_; lean_object* v_eAssignment_2225_; uint8_t v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2223_ = lean_st_ref_get(v___y_2221_);
v_mctx_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc_ref(v_mctx_2224_);
lean_dec(v___x_2223_);
v_eAssignment_2225_ = lean_ctor_get(v_mctx_2224_, 8);
lean_inc_ref(v_eAssignment_2225_);
lean_dec_ref(v_mctx_2224_);
v___x_2226_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(v_eAssignment_2225_, v_mvarId_2220_);
lean_dec_ref(v_eAssignment_2225_);
v___x_2227_ = lean_box(v___x_2226_);
v___x_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg___boxed(lean_object* v_mvarId_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(v_mvarId_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec(v_mvarId_2229_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1(size_t v_sz_2233_, size_t v_i_2234_, lean_object* v_bs_2235_){
_start:
{
uint8_t v___x_2236_; 
v___x_2236_ = lean_usize_dec_lt(v_i_2234_, v_sz_2233_);
if (v___x_2236_ == 0)
{
return v_bs_2235_;
}
else
{
lean_object* v_v_2237_; lean_object* v_name_2238_; lean_object* v_type_2239_; lean_object* v_value_2240_; lean_object* v___x_2241_; lean_object* v_bs_x27_2242_; uint8_t v___x_2243_; uint8_t v___x_2244_; lean_object* v___x_2245_; size_t v___x_2246_; size_t v___x_2247_; lean_object* v___x_2248_; 
v_v_2237_ = lean_array_uget_borrowed(v_bs_2235_, v_i_2234_);
v_name_2238_ = lean_ctor_get(v_v_2237_, 0);
lean_inc(v_name_2238_);
v_type_2239_ = lean_ctor_get(v_v_2237_, 1);
lean_inc_ref(v_type_2239_);
v_value_2240_ = lean_ctor_get(v_v_2237_, 2);
lean_inc_ref(v_value_2240_);
v___x_2241_ = lean_unsigned_to_nat(0u);
v_bs_x27_2242_ = lean_array_uset(v_bs_2235_, v_i_2234_, v___x_2241_);
v___x_2243_ = 0;
v___x_2244_ = 0;
v___x_2245_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2245_, 0, v_name_2238_);
lean_ctor_set(v___x_2245_, 1, v_type_2239_);
lean_ctor_set(v___x_2245_, 2, v_value_2240_);
lean_ctor_set_uint8(v___x_2245_, sizeof(void*)*3, v___x_2243_);
lean_ctor_set_uint8(v___x_2245_, sizeof(void*)*3 + 1, v___x_2244_);
v___x_2246_ = ((size_t)1ULL);
v___x_2247_ = lean_usize_add(v_i_2234_, v___x_2246_);
v___x_2248_ = lean_array_uset(v_bs_x27_2242_, v_i_2234_, v___x_2245_);
v_i_2234_ = v___x_2247_;
v_bs_2235_ = v___x_2248_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1___boxed(lean_object* v_sz_2250_, lean_object* v_i_2251_, lean_object* v_bs_2252_){
_start:
{
size_t v_sz_boxed_2253_; size_t v_i_boxed_2254_; lean_object* v_res_2255_; 
v_sz_boxed_2253_ = lean_unbox_usize(v_sz_2250_);
lean_dec(v_sz_2250_);
v_i_boxed_2254_ = lean_unbox_usize(v_i_2251_);
lean_dec(v_i_2251_);
v_res_2255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1(v_sz_boxed_2253_, v_i_boxed_2254_, v_bs_2252_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize(lean_object* v_x_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v___x_2271_; uint8_t v___x_2272_; 
v___x_2271_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0));
lean_inc(v_x_2261_);
v___x_2272_ = l_Lean_Syntax_isOfKind(v_x_2261_, v___x_2271_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2273_; 
lean_dec(v_x_2261_);
v___x_2273_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2273_;
}
else
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; uint8_t v___x_2277_; lean_object* v_types_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2287_; 
v___x_2274_ = lean_unsigned_to_nat(1u);
v___x_2275_ = l_Lean_Syntax_getArg(v_x_2261_, v___x_2274_);
v___x_2276_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_2275_);
v___x_2277_ = l_Lean_Syntax_isOfKind(v___x_2275_, v___x_2276_);
if (v___x_2277_ == 0)
{
lean_object* v___x_2398_; 
lean_dec(v___x_2275_);
lean_dec(v_x_2261_);
v___x_2398_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2398_;
}
else
{
lean_object* v___x_2399_; lean_object* v___x_2400_; uint8_t v___x_2401_; 
v___x_2399_ = lean_unsigned_to_nat(2u);
v___x_2400_ = l_Lean_Syntax_getArg(v_x_2261_, v___x_2399_);
lean_dec(v_x_2261_);
v___x_2401_ = l_Lean_Syntax_isNone(v___x_2400_);
if (v___x_2401_ == 0)
{
uint8_t v___x_2402_; 
lean_inc(v___x_2400_);
v___x_2402_ = l_Lean_Syntax_matchesNull(v___x_2400_, v___x_2274_);
if (v___x_2402_ == 0)
{
lean_object* v___x_2403_; 
lean_dec(v___x_2400_);
lean_dec(v___x_2275_);
v___x_2403_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2403_;
}
else
{
lean_object* v___x_2404_; lean_object* v_types_2405_; lean_object* v___x_2406_; uint8_t v___x_2407_; 
v___x_2404_ = lean_unsigned_to_nat(0u);
v_types_2405_ = l_Lean_Syntax_getArg(v___x_2400_, v___x_2404_);
lean_dec(v___x_2400_);
v___x_2406_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_types_2405_);
v___x_2407_ = l_Lean_Syntax_isOfKind(v_types_2405_, v___x_2406_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2408_; 
lean_dec(v_types_2405_);
lean_dec(v___x_2275_);
v___x_2408_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2408_;
}
else
{
lean_object* v___x_2409_; 
v___x_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2409_, 0, v_types_2405_);
v_types_2279_ = v___x_2409_;
v___y_2280_ = v_a_2262_;
v___y_2281_ = v_a_2263_;
v___y_2282_ = v_a_2264_;
v___y_2283_ = v_a_2265_;
v___y_2284_ = v_a_2266_;
v___y_2285_ = v_a_2267_;
v___y_2286_ = v_a_2268_;
v___y_2287_ = v_a_2269_;
goto v___jp_2278_;
}
}
}
else
{
lean_object* v___x_2410_; 
lean_dec(v___x_2400_);
v___x_2410_ = lean_box(0);
v_types_2279_ = v___x_2410_;
v___y_2280_ = v_a_2262_;
v___y_2281_ = v_a_2263_;
v___y_2282_ = v_a_2264_;
v___y_2283_ = v_a_2265_;
v___y_2284_ = v_a_2266_;
v___y_2285_ = v_a_2267_;
v___y_2286_ = v_a_2268_;
v___y_2287_ = v_a_2269_;
goto v___jp_2278_;
}
}
v___jp_2278_:
{
lean_object* v___x_2288_; 
v___x_2288_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_2286_, v___y_2287_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2396_; 
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2396_ == 0)
{
lean_object* v_unused_2397_; 
v_unused_2397_ = lean_ctor_get(v___x_2288_, 0);
lean_dec(v_unused_2397_);
v___x_2290_ = v___x_2288_;
v_isShared_2291_ = v_isSharedCheck_2396_;
goto v_resetjp_2289_;
}
else
{
lean_dec(v___x_2288_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2396_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2292_; uint8_t v___x_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2292_ = lean_unsigned_to_nat(10u);
v___x_2293_ = 0;
v___x_2294_ = lean_unsigned_to_nat(100000u);
v___x_2295_ = 0;
v___x_2296_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_2296_, 0, v___x_2292_);
lean_ctor_set(v___x_2296_, 1, v___x_2294_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*2, v___x_2277_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*2 + 1, v___x_2277_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*2 + 2, v___x_2293_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*2 + 3, v___x_2277_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*2 + 4, v___x_2277_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*2 + 5, v___x_2277_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*2 + 6, v___x_2277_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*2 + 7, v___x_2277_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*2 + 8, v___x_2293_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*2 + 9, v___x_2293_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*2 + 10, v___x_2295_);
v___x_2297_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_2275_, v___x_2296_, v___x_2277_, v___y_2280_, v___y_2286_, v___y_2287_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2299_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
lean_dec_ref_known(v___x_2297_, 1);
v___x_2299_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_types_2279_, v___y_2286_, v___y_2287_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2301_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v___x_2301_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2281_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2302_);
lean_dec_ref_known(v___x_2301_, 1);
v___x_2303_ = lean_unsigned_to_nat(9u);
v___x_2304_ = lean_unsigned_to_nat(5u);
v___x_2305_ = lean_unsigned_to_nat(8u);
v___x_2306_ = lean_unsigned_to_nat(1000u);
v___x_2307_ = lean_unsigned_to_nat(1024u);
v___x_2308_ = lean_unsigned_to_nat(10000u);
v___x_2309_ = lean_unsigned_to_nat(1048576u);
v___x_2310_ = lean_unsigned_to_nat(50u);
v___x_2311_ = lean_box(0);
v___x_2312_ = lean_alloc_ctor(0, 14, 32);
lean_ctor_set(v___x_2312_, 0, v___x_2303_);
lean_ctor_set(v___x_2312_, 1, v___x_2304_);
lean_ctor_set(v___x_2312_, 2, v___x_2305_);
lean_ctor_set(v___x_2312_, 3, v___x_2305_);
lean_ctor_set(v___x_2312_, 4, v___x_2306_);
lean_ctor_set(v___x_2312_, 5, v___x_2306_);
lean_ctor_set(v___x_2312_, 6, v___x_2294_);
lean_ctor_set(v___x_2312_, 7, v___x_2307_);
lean_ctor_set(v___x_2312_, 8, v___x_2308_);
lean_ctor_set(v___x_2312_, 9, v___x_2306_);
lean_ctor_set(v___x_2312_, 10, v___x_2309_);
lean_ctor_set(v___x_2312_, 11, v___x_2292_);
lean_ctor_set(v___x_2312_, 12, v___x_2310_);
lean_ctor_set(v___x_2312_, 13, v___x_2311_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14, v___x_2293_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 1, v___x_2293_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 2, v___x_2293_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 3, v___x_2293_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 4, v___x_2293_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 5, v___x_2277_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 6, v___x_2277_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 7, v___x_2277_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 8, v___x_2293_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 9, v___x_2293_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 10, v___x_2277_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 11, v___x_2293_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 12, v___x_2277_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 13, v___x_2277_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 14, v___x_2277_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 15, v___x_2277_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 16, v___x_2277_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 17, v___x_2293_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 18, v___x_2277_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 19, v___x_2277_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 20, v___x_2277_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 21, v___x_2277_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 22, v___x_2277_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 23, v___x_2277_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 24, v___x_2277_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 25, v___x_2277_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 26, v___x_2277_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 27, v___x_2277_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 28, v___x_2277_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 29, v___x_2293_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 30, v___x_2277_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*14 + 31, v___x_2277_);
v___x_2313_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_2312_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2315_; lean_object* v___x_2317_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref_known(v___x_2313_, 1);
v___x_2315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2315_, 0, v_a_2298_);
lean_ctor_set(v___x_2315_, 1, v_a_2300_);
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v_a_2302_);
v___x_2317_ = v___x_2290_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2302_);
v___x_2317_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
lean_object* v___x_2318_; lean_object* v___f_2319_; lean_object* v___x_2320_; 
v___x_2318_ = lean_box(v___x_2293_);
v___f_2319_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0___boxed), 13, 3);
lean_closure_set(v___f_2319_, 0, v___x_2317_);
lean_closure_set(v___f_2319_, 1, v___x_2318_);
lean_closure_set(v___f_2319_, 2, v___x_2315_);
v___x_2320_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___f_2319_, v_a_2314_, v___x_2311_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v_snd_2322_; lean_object* v_target_2323_; lean_object* v_hypotheses_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v_a_2327_; uint8_t v___x_2328_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2320_, 1);
v_snd_2322_ = lean_ctor_get(v_a_2321_, 1);
lean_inc(v_snd_2322_);
lean_dec(v_a_2321_);
v_target_2323_ = lean_ctor_get(v_snd_2322_, 4);
lean_inc_ref(v_target_2323_);
v_hypotheses_2324_ = lean_ctor_get(v_snd_2322_, 5);
lean_inc_ref(v_hypotheses_2324_);
lean_dec(v_snd_2322_);
v___x_2325_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_2323_);
lean_dec_ref(v_target_2323_);
v___x_2326_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(v___x_2325_, v___y_2285_);
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2327_);
lean_dec_ref(v___x_2326_);
v___x_2328_ = lean_unbox(v_a_2327_);
lean_dec(v_a_2327_);
if (v___x_2328_ == 0)
{
size_t v_sz_2329_; size_t v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v_sz_2329_ = lean_array_size(v_hypotheses_2324_);
v___x_2330_ = ((size_t)0ULL);
v___x_2331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1(v_sz_2329_, v___x_2330_, v_hypotheses_2324_);
v___x_2332_ = l_Lean_MVarId_assertHypotheses(v___x_2325_, v___x_2331_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v_snd_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2343_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2332_, 1);
v_snd_2334_ = lean_ctor_get(v_a_2333_, 1);
v_isSharedCheck_2343_ = !lean_is_exclusive(v_a_2333_);
if (v_isSharedCheck_2343_ == 0)
{
lean_object* v_unused_2344_; 
v_unused_2344_ = lean_ctor_get(v_a_2333_, 0);
lean_dec(v_unused_2344_);
v___x_2336_ = v_a_2333_;
v_isShared_2337_ = v_isSharedCheck_2343_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_snd_2334_);
lean_dec(v_a_2333_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2343_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2338_ = lean_box(0);
if (v_isShared_2337_ == 0)
{
lean_ctor_set_tag(v___x_2336_, 1);
lean_ctor_set(v___x_2336_, 1, v___x_2338_);
lean_ctor_set(v___x_2336_, 0, v_snd_2334_);
v___x_2340_ = v___x_2336_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_snd_2334_);
lean_ctor_set(v_reuseFailAlloc_2342_, 1, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
lean_object* v___x_2341_; 
v___x_2341_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2340_, v___y_2281_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
return v___x_2341_;
}
}
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
v_a_2345_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2332_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2332_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
else
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
lean_dec(v___x_2325_);
lean_dec_ref(v_hypotheses_2324_);
v___x_2353_ = lean_box(0);
v___x_2354_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2353_, v___y_2281_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
return v___x_2354_;
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
v_a_2355_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2320_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2320_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec(v_a_2302_);
lean_dec(v_a_2300_);
lean_dec(v_a_2298_);
lean_del_object(v___x_2290_);
v_a_2364_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2313_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2313_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
lean_dec(v_a_2300_);
lean_dec(v_a_2298_);
lean_del_object(v___x_2290_);
v_a_2372_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2301_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2301_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
lean_dec(v_a_2298_);
lean_del_object(v___x_2290_);
v_a_2380_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2299_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2299_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
lean_del_object(v___x_2290_);
lean_dec(v_types_2279_);
v_a_2388_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2390_ = v___x_2297_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2297_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
}
else
{
lean_dec(v_types_2279_);
lean_dec(v___x_2275_);
return v___x_2288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___boxed(lean_object* v_x_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_Lean_Elab_Tactic_BVDecide_evalBVNormalize(v_x_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
lean_dec(v_a_2419_);
lean_dec_ref(v_a_2418_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0(lean_object* v_mvarId_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(v_mvarId_2422_, v___y_2428_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___boxed(lean_object* v_mvarId_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0(v_mvarId_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v_mvarId_2433_);
return v_res_2443_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0(lean_object* v_00_u03b2_2444_, lean_object* v_x_2445_, lean_object* v_x_2446_){
_start:
{
uint8_t v___x_2447_; 
v___x_2447_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(v_x_2445_, v_x_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2448_, lean_object* v_x_2449_, lean_object* v_x_2450_){
_start:
{
uint8_t v_res_2451_; lean_object* v_r_2452_; 
v_res_2451_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0(v_00_u03b2_2448_, v_x_2449_, v_x_2450_);
lean_dec(v_x_2450_);
lean_dec_ref(v_x_2449_);
v_r_2452_ = lean_box(v_res_2451_);
return v_r_2452_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2453_, lean_object* v_x_2454_, size_t v_x_2455_, lean_object* v_x_2456_){
_start:
{
uint8_t v___x_2457_; 
v___x_2457_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_2454_, v_x_2455_, v_x_2456_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2458_, lean_object* v_x_2459_, lean_object* v_x_2460_, lean_object* v_x_2461_){
_start:
{
size_t v_x_5120__boxed_2462_; uint8_t v_res_2463_; lean_object* v_r_2464_; 
v_x_5120__boxed_2462_ = lean_unbox_usize(v_x_2460_);
lean_dec(v_x_2460_);
v_res_2463_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1(v_00_u03b2_2458_, v_x_2459_, v_x_5120__boxed_2462_, v_x_2461_);
lean_dec(v_x_2461_);
lean_dec_ref(v_x_2459_);
v_r_2464_ = lean_box(v_res_2463_);
return v_r_2464_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2465_, lean_object* v_keys_2466_, lean_object* v_vals_2467_, lean_object* v_heq_2468_, lean_object* v_i_2469_, lean_object* v_k_2470_){
_start:
{
uint8_t v___x_2471_; 
v___x_2471_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2466_, v_i_2469_, v_k_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2472_, lean_object* v_keys_2473_, lean_object* v_vals_2474_, lean_object* v_heq_2475_, lean_object* v_i_2476_, lean_object* v_k_2477_){
_start:
{
uint8_t v_res_2478_; lean_object* v_r_2479_; 
v_res_2478_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2472_, v_keys_2473_, v_vals_2474_, v_heq_2475_, v_i_2476_, v_k_2477_);
lean_dec(v_k_2477_);
lean_dec_ref(v_vals_2474_);
lean_dec_ref(v_keys_2473_);
v_r_2479_ = lean_box(v_res_2478_);
return v_r_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1(){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2488_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2489_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0));
v___x_2490_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___closed__1));
v___x_2491_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___boxed), 10, 0);
v___x_2492_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2488_, v___x_2489_, v___x_2490_, v___x_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___boxed(lean_object* v_a_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1();
return v_res_2494_;
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
