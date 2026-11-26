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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkDefaultParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_fileName(lean_object*);
lean_object* l_Lean_Elab_Term_getDeclName_x3f___redArg(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_remove_file(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_LRAT_trim(lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(lean_object*, lean_object*, uint8_t);
lean_object* lean_io_create_tempfile();
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__7;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_normalize_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_normalize_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_check_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_check_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_decide_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_decide_elim(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__0_value;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "tacticHave__"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(57, 244, 114, 225, 1, 158, 79, 25)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "have"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__9_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__9_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__11_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__11_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__13_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__14;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__15_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__15_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__16_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__17_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__18_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__17_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__18_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__18_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__18_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__19_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__20_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__17_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__20_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__20_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(178, 14, 254, 151, 151, 84, 196, 42)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__20_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__20_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__21_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__22_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__17_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__22_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__22_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__23 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__23_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__24_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__16_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__24_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__25 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__25_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__21_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__25_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__26 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__26_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__19_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__26_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__27 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__27_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__16_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__27_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__28 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__28_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__29 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__29_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__30_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__30_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__30_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__29_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__30 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__30_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__31 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__31_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__32 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__32_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__33 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__33_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__34_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__34_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__34_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__33_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__34 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__34_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__35 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__35_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "bvNormalize"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "bv_normalize"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvCheck"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "bv_check"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_decide"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___boxed__const__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___boxed(lean_object**);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "This goal can be closed by only applying bv_normalize, no need to keep the LRAT proof around."};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(237, 160, 246, 114, 147, 242, 134, 91)}};
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 99, 199, 244, 147, 253, 171, 138)}};
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
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_24_; lean_object* v_toCold_25_; lean_object* v_env_26_; lean_object* v_options_27_; uint8_t v___x_28_; lean_object* v_env_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_24_ = lean_st_ref_get(v___y_22_);
v_toCold_25_ = lean_ctor_get(v___y_21_, 0);
v_env_26_ = lean_ctor_get(v___x_24_, 0);
lean_inc_ref(v_env_26_);
lean_dec(v___x_24_);
v_options_27_ = lean_ctor_get(v_toCold_25_, 2);
v___x_28_ = 0;
v_env_29_ = l_Lean_Environment_setRecordingDeps(v_env_26_, v___x_28_);
v___x_30_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__2);
v___x_31_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_27_);
v___x_32_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_32_, 0, v_env_29_);
lean_ctor_set(v___x_32_, 1, v___x_30_);
lean_ctor_set(v___x_32_, 2, v___x_31_);
lean_ctor_set(v___x_32_, 3, v_options_27_);
v___x_33_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
lean_ctor_set(v___x_33_, 1, v_msgData_20_);
v___x_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___boxed(lean_object* v_msgData_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0(v_msgData_35_, v___y_36_, v___y_37_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg(lean_object* v_msg_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_ref_44_; lean_object* v___x_45_; lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_54_; 
v_ref_44_ = lean_ctor_get(v___y_41_, 2);
v___x_45_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0(v_msg_40_, v___y_41_, v___y_42_);
v_a_46_ = lean_ctor_get(v___x_45_, 0);
v_isSharedCheck_54_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_54_ == 0)
{
v___x_48_ = v___x_45_;
v_isShared_49_ = v_isSharedCheck_54_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v___x_45_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_54_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_50_; lean_object* v___x_52_; 
lean_inc(v_ref_44_);
v___x_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_50_, 0, v_ref_44_);
lean_ctor_set(v___x_50_, 1, v_a_46_);
if (v_isShared_49_ == 0)
{
lean_ctor_set_tag(v___x_48_, 1);
lean_ctor_set(v___x_48_, 0, v___x_50_);
v___x_52_ = v___x_48_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_50_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg___boxed(lean_object* v_msg_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg(v_msg_55_, v___y_56_, v___y_57_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
return v_res_59_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__5(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__4));
v___x_69_ = l_Lean_stringToMessageData(v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v___x_73_; lean_object* v_env_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = lean_st_ref_get(v_a_71_);
v_env_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc_ref(v_env_74_);
lean_dec(v___x_73_);
v___x_75_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__3));
v___x_76_ = l_Lean_Environment_getModuleIdx_x3f(v_env_74_, v___x_75_);
lean_dec_ref(v_env_74_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__5, &l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__5);
v___x_78_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg(v___x_77_, v_a_70_, v_a_71_);
return v___x_78_;
}
else
{
lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_86_; 
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_86_ == 0)
{
lean_object* v_unused_87_; 
v_unused_87_ = lean_ctor_get(v___x_76_, 0);
lean_dec(v_unused_87_);
v___x_80_ = v___x_76_;
v_isShared_81_ = v_isSharedCheck_86_;
goto v_resetjp_79_;
}
else
{
lean_dec(v___x_76_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_86_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_82_; lean_object* v___x_84_; 
v___x_82_ = lean_box(0);
if (v_isShared_81_ == 0)
{
lean_ctor_set_tag(v___x_80_, 0);
lean_ctor_set(v___x_80_, 0, v___x_82_);
v___x_84_ = v___x_80_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_82_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___boxed(lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v_a_88_, v_a_89_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0(lean_object* v_00_u03b1_92_, lean_object* v_msg_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg(v_msg_93_, v___y_94_, v___y_95_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___boxed(lean_object* v_00_u03b1_98_, lean_object* v_msg_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0(v_00_u03b1_98_, v_msg_99_, v___y_100_, v___y_101_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(lean_object* v_msgData_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v___x_110_; lean_object* v_env_111_; uint8_t v___x_112_; lean_object* v_env_113_; lean_object* v___x_114_; lean_object* v_toCold_115_; lean_object* v_mctx_116_; lean_object* v_lctx_117_; lean_object* v_options_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_110_ = lean_st_ref_get(v___y_108_);
v_env_111_ = lean_ctor_get(v___x_110_, 0);
lean_inc_ref(v_env_111_);
lean_dec(v___x_110_);
v___x_112_ = 0;
v_env_113_ = l_Lean_Environment_setRecordingDeps(v_env_111_, v___x_112_);
v___x_114_ = lean_st_ref_get(v___y_106_);
v_toCold_115_ = lean_ctor_get(v___y_107_, 0);
v_mctx_116_ = lean_ctor_get(v___x_114_, 0);
lean_inc_ref(v_mctx_116_);
lean_dec(v___x_114_);
v_lctx_117_ = lean_ctor_get(v___y_105_, 2);
v_options_118_ = lean_ctor_get(v_toCold_115_, 2);
lean_inc_ref(v_options_118_);
lean_inc_ref(v_lctx_117_);
v___x_119_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_119_, 0, v_env_113_);
lean_ctor_set(v___x_119_, 1, v_mctx_116_);
lean_ctor_set(v___x_119_, 2, v_lctx_117_);
lean_ctor_set(v___x_119_, 3, v_options_118_);
v___x_120_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v_msgData_104_);
v___x_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0___boxed(lean_object* v_msgData_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v_msgData_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
return v_res_128_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_box(1);
v___x_130_ = l_Lean_MessageData_ofFormat(v___x_129_);
return v___x_130_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__2));
v___x_135_ = l_Lean_MessageData_ofFormat(v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3(lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
if (lean_obj_tag(v_x_137_) == 0)
{
return v_x_136_;
}
else
{
lean_object* v_head_138_; lean_object* v_tail_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_161_; 
v_head_138_ = lean_ctor_get(v_x_137_, 0);
v_tail_139_ = lean_ctor_get(v_x_137_, 1);
v_isSharedCheck_161_ = !lean_is_exclusive(v_x_137_);
if (v_isSharedCheck_161_ == 0)
{
v___x_141_ = v_x_137_;
v_isShared_142_ = v_isSharedCheck_161_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_tail_139_);
lean_inc(v_head_138_);
lean_dec(v_x_137_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_161_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v_before_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_159_; 
v_before_143_ = lean_ctor_get(v_head_138_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v_head_138_);
if (v_isSharedCheck_159_ == 0)
{
lean_object* v_unused_160_; 
v_unused_160_ = lean_ctor_get(v_head_138_, 1);
lean_dec(v_unused_160_);
v___x_145_ = v_head_138_;
v_isShared_146_ = v_isSharedCheck_159_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_before_143_);
lean_dec(v_head_138_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_159_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_147_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_146_ == 0)
{
lean_ctor_set_tag(v___x_145_, 7);
lean_ctor_set(v___x_145_, 1, v___x_147_);
lean_ctor_set(v___x_145_, 0, v_x_136_);
v___x_149_ = v___x_145_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_x_136_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v___x_147_);
v___x_149_ = v_reuseFailAlloc_158_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_150_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_142_ == 0)
{
lean_ctor_set_tag(v___x_141_, 7);
lean_ctor_set(v___x_141_, 1, v___x_150_);
lean_ctor_set(v___x_141_, 0, v___x_149_);
v___x_152_ = v___x_141_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_149_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v___x_150_);
v___x_152_ = v_reuseFailAlloc_157_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_153_ = l_Lean_MessageData_ofSyntax(v_before_143_);
v___x_154_ = l_Lean_indentD(v___x_153_);
v___x_155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_152_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
v_x_136_ = v___x_155_;
v_x_137_ = v_tail_139_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(lean_object* v_opts_162_, lean_object* v_opt_163_){
_start:
{
lean_object* v_name_164_; lean_object* v_defValue_165_; lean_object* v_map_166_; lean_object* v___x_167_; 
v_name_164_ = lean_ctor_get(v_opt_163_, 0);
v_defValue_165_ = lean_ctor_get(v_opt_163_, 1);
v_map_166_ = lean_ctor_get(v_opts_162_, 0);
v___x_167_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_166_, v_name_164_);
if (lean_obj_tag(v___x_167_) == 0)
{
uint8_t v___x_168_; 
v___x_168_ = lean_unbox(v_defValue_165_);
return v___x_168_;
}
else
{
lean_object* v_val_169_; 
v_val_169_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_val_169_);
lean_dec_ref_known(v___x_167_, 1);
if (lean_obj_tag(v_val_169_) == 1)
{
uint8_t v_v_170_; 
v_v_170_ = lean_ctor_get_uint8(v_val_169_, 0);
lean_dec_ref_known(v_val_169_, 0);
return v_v_170_;
}
else
{
uint8_t v___x_171_; 
lean_dec(v_val_169_);
v___x_171_ = lean_unbox(v_defValue_165_);
return v___x_171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_172_, lean_object* v_opt_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_opts_172_, v_opt_173_);
lean_dec_ref(v_opt_173_);
lean_dec_ref(v_opts_172_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__1));
v___x_180_ = l_Lean_MessageData_ofFormat(v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(lean_object* v_msgData_181_, lean_object* v_macroStack_182_, lean_object* v___y_183_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_185_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_183_);
v___x_186_ = l_Lean_Elab_pp_macroStack;
v___x_187_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v___x_185_, v___x_186_);
lean_dec_ref(v___x_185_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; 
lean_dec(v_macroStack_182_);
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v_msgData_181_);
return v___x_188_;
}
else
{
if (lean_obj_tag(v_macroStack_182_) == 0)
{
lean_object* v___x_189_; 
v___x_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_189_, 0, v_msgData_181_);
return v___x_189_;
}
else
{
lean_object* v_head_190_; lean_object* v_after_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_206_; 
v_head_190_ = lean_ctor_get(v_macroStack_182_, 0);
lean_inc(v_head_190_);
v_after_191_ = lean_ctor_get(v_head_190_, 1);
v_isSharedCheck_206_ = !lean_is_exclusive(v_head_190_);
if (v_isSharedCheck_206_ == 0)
{
lean_object* v_unused_207_; 
v_unused_207_ = lean_ctor_get(v_head_190_, 0);
lean_dec(v_unused_207_);
v___x_193_ = v_head_190_;
v_isShared_194_ = v_isSharedCheck_206_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_after_191_);
lean_dec(v_head_190_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_206_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_195_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_194_ == 0)
{
lean_ctor_set_tag(v___x_193_, 7);
lean_ctor_set(v___x_193_, 1, v___x_195_);
lean_ctor_set(v___x_193_, 0, v_msgData_181_);
v___x_197_ = v___x_193_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_msgData_181_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___x_195_);
v___x_197_ = v_reuseFailAlloc_205_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v_msgData_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_198_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2);
v___x_199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_197_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = l_Lean_MessageData_ofSyntax(v_after_191_);
v___x_201_ = l_Lean_indentD(v___x_200_);
v_msgData_202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_202_, 0, v___x_199_);
lean_ctor_set(v_msgData_202_, 1, v___x_201_);
v___x_203_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3(v_msgData_202_, v_macroStack_182_);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_208_, lean_object* v_macroStack_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_msgData_208_, v_macroStack_209_, v___y_210_);
lean_dec_ref(v___y_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(lean_object* v_msg_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_ref_221_; lean_object* v_macroStack_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v_a_225_; lean_object* v___x_226_; lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_235_; 
v_ref_221_ = lean_ctor_get(v___y_218_, 2);
v_macroStack_222_ = lean_ctor_get(v___y_214_, 1);
v___x_223_ = l_Lean_Elab_getBetterRef(v_ref_221_, v_macroStack_222_);
v___x_224_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v_msg_213_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
v_a_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_225_);
lean_dec_ref(v___x_224_);
lean_inc(v_macroStack_222_);
v___x_226_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_a_225_, v_macroStack_222_, v___y_218_);
v_a_227_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_235_ == 0)
{
v___x_229_ = v___x_226_;
v_isShared_230_ = v_isSharedCheck_235_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_226_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_235_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_223_);
lean_ctor_set(v___x_231_, 1, v_a_227_);
if (v_isShared_230_ == 0)
{
lean_ctor_set_tag(v___x_229_, 1);
lean_ctor_set(v___x_229_, 0, v___x_231_);
v___x_233_ = v___x_229_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg___boxed(lean_object* v_msg_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v_msg_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
return v_res_244_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__0));
v___x_247_ = l_Lean_stringToMessageData(v___x_246_);
return v___x_247_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__2));
v___x_250_ = l_Lean_stringToMessageData(v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_toCold_258_; lean_object* v_fileName_259_; lean_object* v___x_260_; 
v_toCold_258_ = lean_ctor_get(v_a_255_, 0);
v_fileName_259_ = lean_ctor_get(v_toCold_258_, 0);
lean_inc_ref(v_fileName_259_);
v___x_260_ = l_System_FilePath_parent(v_fileName_259_);
if (lean_obj_tag(v___x_260_) == 1)
{
lean_object* v_val_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
v_val_261_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_260_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_val_261_);
lean_dec(v___x_260_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
lean_ctor_set_tag(v___x_263_, 0);
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_val_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
lean_dec(v___x_260_);
v___x_269_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1, &l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1);
lean_inc_ref(v_fileName_259_);
v___x_270_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_270_, 0, v_fileName_259_);
v___x_271_ = l_Lean_MessageData_ofFormat(v___x_270_);
v___x_272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_269_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3, &l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3);
v___x_274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v___x_274_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_);
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___boxed(lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
lean_dec(v_a_279_);
lean_dec_ref(v_a_278_);
lean_dec(v_a_277_);
lean_dec_ref(v_a_276_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0(lean_object* v_00_u03b1_284_, lean_object* v_msg_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v_msg_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___boxed(lean_object* v_00_u03b1_294_, lean_object* v_msg_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0(v_00_u03b1_294_, v_msg_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1(lean_object* v_msgData_304_, lean_object* v_macroStack_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_msgData_304_, v_macroStack_305_, v___y_310_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___boxed(lean_object* v_msgData_314_, lean_object* v_macroStack_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1(v_msgData_314_, v_macroStack_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(lean_object* v_lratPath_324_, lean_object* v_cfg_325_, lean_object* v_types_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_335_);
lean_dec_ref_known(v___x_334_, 1);
v___x_336_ = l_System_FilePath_join(v_a_335_, v_lratPath_324_);
v___x_337_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new(v___x_336_, v_cfg_325_, v_types_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
return v___x_337_;
}
else
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
lean_dec(v_types_326_);
lean_dec_ref(v_cfg_325_);
lean_dec_ref(v_lratPath_324_);
v_a_338_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_334_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_334_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext___boxed(lean_object* v_lratPath_346_, lean_object* v_cfg_347_, lean_object* v_types_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v_lratPath_346_, v_cfg_347_, v_types_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0(lean_object* v_g_357_, lean_object* v___x_358_, lean_object* v___x_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(v_g_357_, v___x_358_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; 
v_unused_380_ = lean_ctor_get(v___x_372_, 0);
lean_dec(v_unused_380_);
v___x_374_ = v___x_372_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_dec(v___x_372_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_359_);
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_359_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
v_a_381_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_372_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_372_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0___boxed(lean_object* v_g_389_, lean_object* v___x_390_, lean_object* v___x_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0(v_g_389_, v___x_390_, v___x_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(lean_object* v_g_405_, lean_object* v_hypotheses_406_, lean_object* v_ctx_407_, lean_object* v_epr_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_config_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___f_422_; lean_object* v___x_423_; 
v_config_419_ = lean_ctor_get(v_ctx_407_, 5);
lean_inc_ref(v_config_419_);
v___x_420_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed), 16, 1);
lean_closure_set(v___x_420_, 0, v_ctx_407_);
v___x_421_ = lean_box(0);
v___f_422_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0___boxed), 15, 3);
lean_closure_set(v___f_422_, 0, v_g_405_);
lean_closure_set(v___f_422_, 1, v___x_420_);
lean_closure_set(v___f_422_, 2, v___x_421_);
v___x_423_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg(v___f_422_, v_hypotheses_406_, v_config_419_, v_epr_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___boxed(lean_object* v_g_424_, lean_object* v_hypotheses_425_, lean_object* v_ctx_426_, lean_object* v_epr_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(v_g_424_, v_hypotheses_425_, v_ctx_426_, v_epr_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
return v_res_438_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__0);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
return v___x_440_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0);
v___x_442_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
lean_ctor_set(v___x_442_, 2, v___x_441_);
lean_ctor_set(v___x_442_, 3, v___x_441_);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = lean_box(0);
v___x_444_ = lean_unsigned_to_nat(16u);
v___x_445_ = lean_mk_array(v___x_444_, v___x_443_);
return v___x_445_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_446_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2);
v___x_447_ = lean_unsigned_to_nat(0u);
v___x_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v___x_446_);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3);
v___x_450_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
lean_ctor_set(v___x_450_, 2, v___x_449_);
lean_ctor_set(v___x_450_, 3, v___x_449_);
return v___x_450_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__7(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_455_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6));
v___x_456_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3);
v___x_457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
lean_ctor_set(v___x_457_, 2, v___x_456_);
lean_ctor_set(v___x_457_, 3, v___x_455_);
lean_ctor_set(v___x_457_, 4, v___x_455_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck(lean_object* v_target_458_, lean_object* v_ctx_459_, lean_object* v_warn_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___y_481_; lean_object* v___x_491_; 
lean_inc_ref(v_ctx_459_);
v___x_471_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_ctx_459_);
v___x_472_ = lean_box(0);
v___x_473_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1);
v___x_474_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4);
v___x_475_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5));
v___x_476_ = 0;
v___x_477_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__7, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__7);
v___x_478_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_478_, 0, v___x_473_);
lean_ctor_set(v___x_478_, 1, v___x_474_);
lean_ctor_set(v___x_478_, 2, v_target_458_);
lean_ctor_set(v___x_478_, 3, v___x_475_);
lean_ctor_set(v___x_478_, 4, v___x_477_);
lean_ctor_set_uint8(v___x_478_, sizeof(void*)*5, v___x_476_);
v___x_479_ = lean_st_mk_ref(v___x_478_);
v___x_491_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_472_, v___x_471_, v___x_479_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_);
lean_dec_ref(v___x_471_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; uint8_t v___x_493_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
lean_dec_ref_known(v___x_491_, 1);
v___x_493_ = lean_unbox(v_a_492_);
lean_dec(v_a_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; lean_object* v_eprBvProblem_495_; lean_object* v___x_496_; lean_object* v_target_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v_hypotheses_500_; lean_object* v___x_501_; 
lean_dec_ref(v_warn_460_);
v___x_494_ = lean_st_ref_get(v___x_479_);
v_eprBvProblem_495_ = lean_ctor_get(v___x_494_, 4);
lean_inc_ref(v_eprBvProblem_495_);
lean_dec(v___x_494_);
v___x_496_ = lean_st_ref_get(v___x_479_);
v_target_497_ = lean_ctor_get(v___x_496_, 2);
lean_inc_ref(v_target_497_);
lean_dec(v___x_496_);
v___x_498_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_497_);
lean_dec_ref(v_target_497_);
v___x_499_ = lean_st_ref_get(v___x_479_);
v_hypotheses_500_ = lean_ctor_get(v___x_499_, 3);
lean_inc_ref(v_hypotheses_500_);
lean_dec(v___x_499_);
v___x_501_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(v___x_498_, v_hypotheses_500_, v_ctx_459_, v_eprBvProblem_495_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_);
v___y_481_ = v___x_501_;
goto v___jp_480_;
}
else
{
lean_object* v___x_502_; 
lean_dec_ref(v_ctx_459_);
lean_inc(v_a_469_);
lean_inc_ref(v_a_468_);
lean_inc(v_a_467_);
lean_inc_ref(v_a_466_);
v___x_502_ = lean_apply_5(v_warn_460_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, lean_box(0));
v___y_481_ = v___x_502_;
goto v___jp_480_;
}
}
else
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
lean_dec(v___x_479_);
lean_dec_ref(v_warn_460_);
lean_dec_ref(v_ctx_459_);
v_a_503_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_491_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_491_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
v___jp_480_:
{
if (lean_obj_tag(v___y_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_490_; 
v_a_482_ = lean_ctor_get(v___y_481_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___y_481_);
if (v_isSharedCheck_490_ == 0)
{
v___x_484_ = v___y_481_;
v_isShared_485_ = v_isSharedCheck_490_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___y_481_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_490_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_486_ = lean_st_ref_get(v___x_479_);
lean_dec(v___x_479_);
lean_dec(v___x_486_);
if (v_isShared_485_ == 0)
{
v___x_488_ = v___x_484_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_482_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
else
{
lean_dec(v___x_479_);
return v___y_481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed(lean_object* v_target_511_, lean_object* v_ctx_512_, lean_object* v_warn_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck(v_target_511_, v_ctx_512_, v_warn_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(lean_object* v___y_525_){
_start:
{
lean_object* v_ref_527_; uint8_t v___x_528_; lean_object* v___x_529_; 
v_ref_527_ = lean_ctor_get(v___y_525_, 2);
v___x_528_ = 0;
v___x_529_ = l_Lean_Syntax_getPos_x3f(v_ref_527_, v___x_528_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
else
{
lean_object* v_val_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
v_val_532_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_529_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_val_532_);
lean_dec(v___x_529_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
lean_ctor_set_tag(v___x_534_, 0);
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_val_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg___boxed(lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v___y_540_);
lean_dec_ref(v___y_540_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0(lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v___y_547_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___boxed(lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0(v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
return v_res_558_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__2));
v___x_563_ = l_Lean_stringToMessageData(v___x_562_);
return v___x_563_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__4));
v___x_566_ = l_Lean_stringToMessageData(v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
lean_object* v_toCold_574_; lean_object* v_fileName_575_; lean_object* v_fileMap_576_; lean_object* v___x_577_; 
v_toCold_574_ = lean_ctor_get(v_a_571_, 0);
v_fileName_575_ = lean_ctor_get(v_toCold_574_, 0);
v_fileMap_576_ = lean_ctor_get(v_toCold_574_, 1);
lean_inc_ref(v_fileName_575_);
v___x_577_ = l_System_FilePath_fileName(v_fileName_575_);
if (lean_obj_tag(v___x_577_) == 1)
{
lean_object* v_val_578_; lean_object* v___x_579_; 
v_val_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_val_578_);
lean_dec_ref_known(v___x_577_, 1);
v___x_579_ = l_Lean_Elab_Term_getDeclName_x3f___redArg(v_a_567_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_a_580_);
lean_dec_ref_known(v___x_579_, 1);
if (lean_obj_tag(v_a_580_) == 1)
{
lean_object* v_val_581_; lean_object* v___x_582_; lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_606_; 
v_val_581_ = lean_ctor_get(v_a_580_, 0);
lean_inc(v_val_581_);
lean_dec_ref_known(v_a_580_, 1);
v___x_582_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v_a_571_);
v_a_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_606_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_606_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_606_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v_line_588_; lean_object* v_column_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
lean_inc_ref(v_fileMap_576_);
v___x_587_ = l_Lean_FileMap_toPosition(v_fileMap_576_, v_a_583_);
lean_dec(v_a_583_);
v_line_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_line_588_);
v_column_589_ = lean_ctor_get(v___x_587_, 1);
lean_inc(v_column_589_);
lean_dec_ref(v___x_587_);
v___x_590_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__0));
v___x_591_ = lean_string_append(v_val_578_, v___x_590_);
v___x_592_ = 1;
v___x_593_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_581_, v___x_592_);
v___x_594_ = lean_string_append(v___x_591_, v___x_593_);
lean_dec_ref(v___x_593_);
v___x_595_ = lean_string_append(v___x_594_, v___x_590_);
v___x_596_ = l_Nat_reprFast(v_line_588_);
v___x_597_ = lean_string_append(v___x_595_, v___x_596_);
lean_dec_ref(v___x_596_);
v___x_598_ = lean_string_append(v___x_597_, v___x_590_);
v___x_599_ = l_Nat_reprFast(v_column_589_);
v___x_600_ = lean_string_append(v___x_598_, v___x_599_);
lean_dec_ref(v___x_599_);
v___x_601_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__1));
v___x_602_ = lean_string_append(v___x_600_, v___x_601_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_602_);
v___x_604_ = v___x_585_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
else
{
lean_object* v___x_607_; lean_object* v___x_608_; 
lean_dec(v_a_580_);
lean_dec(v_val_578_);
v___x_607_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3, &l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3);
v___x_608_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v___x_607_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
return v___x_608_;
}
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec(v_val_578_);
v_a_609_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_579_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_579_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; 
lean_dec(v___x_577_);
v___x_617_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5, &l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5);
v___x_618_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v___x_617_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
return v___x_618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___boxed(lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(lean_object* v_cfg_627_, lean_object* v_types_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_638_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_a_637_);
lean_dec_ref_known(v___x_636_, 1);
v___x_638_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v_a_637_, v_cfg_627_, v_types_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
return v___x_638_;
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec(v_types_628_);
lean_dec_ref(v_cfg_627_);
v_a_639_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_636_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_636_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext___boxed(lean_object* v_cfg_647_, lean_object* v_types_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(v_cfg_647_, v_types_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
lean_dec(v_a_654_);
lean_dec_ref(v_a_653_);
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorIdx___impl(lean_object* v_x_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = lean_obj_tag_nat(v_x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorIdx___impl___boxed(lean_object* v_x_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorIdx___impl(v_x_659_);
lean_dec(v_x_659_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim___redArg(lean_object* v_t_661_, lean_object* v_k_662_){
_start:
{
if (lean_obj_tag(v_t_661_) == 1)
{
lean_object* v_path_663_; lean_object* v___x_664_; 
v_path_663_ = lean_ctor_get(v_t_661_, 0);
lean_inc_ref(v_path_663_);
lean_dec_ref_known(v_t_661_, 1);
v___x_664_ = lean_apply_1(v_k_662_, v_path_663_);
return v___x_664_;
}
else
{
lean_dec(v_t_661_);
return v_k_662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim(lean_object* v_motive_665_, lean_object* v_ctorIdx_666_, lean_object* v_t_667_, lean_object* v_h_668_, lean_object* v_k_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim___redArg(v_t_667_, v_k_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim___boxed(lean_object* v_motive_671_, lean_object* v_ctorIdx_672_, lean_object* v_t_673_, lean_object* v_h_674_, lean_object* v_k_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim(v_motive_671_, v_ctorIdx_672_, v_t_673_, v_h_674_, v_k_675_);
lean_dec(v_ctorIdx_672_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_normalize_elim___redArg(lean_object* v_t_677_, lean_object* v_normalize_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim___redArg(v_t_677_, v_normalize_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_normalize_elim(lean_object* v_motive_680_, lean_object* v_t_681_, lean_object* v_h_682_, lean_object* v_normalize_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim___redArg(v_t_681_, v_normalize_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_check_elim___redArg(lean_object* v_t_685_, lean_object* v_check_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim___redArg(v_t_685_, v_check_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_check_elim(lean_object* v_motive_688_, lean_object* v_t_689_, lean_object* v_h_690_, lean_object* v_check_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim___redArg(v_t_689_, v_check_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_decide_elim___redArg(lean_object* v_t_693_, lean_object* v_decide_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim___redArg(v_t_693_, v_decide_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_decide_elim(lean_object* v_motive_696_, lean_object* v_t_697_, lean_object* v_h_698_, lean_object* v_decide_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim___redArg(v_t_697_, v_decide_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0(lean_object* v_x_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v___x_712_; 
lean_inc(v___y_706_);
lean_inc_ref(v___y_705_);
lean_inc(v___y_704_);
lean_inc_ref(v___y_703_);
lean_inc(v___y_702_);
v___x_712_ = lean_apply_10(v_x_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, lean_box(0));
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0___boxed(lean_object* v_x_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0(v_x_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(lean_object* v_mvarId_725_, lean_object* v_x_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___f_737_; lean_object* v___x_738_; 
lean_inc(v___y_731_);
lean_inc_ref(v___y_730_);
lean_inc(v___y_729_);
lean_inc_ref(v___y_728_);
lean_inc(v___y_727_);
v___f_737_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_737_, 0, v_x_726_);
lean_closure_set(v___f_737_, 1, v___y_727_);
lean_closure_set(v___f_737_, 2, v___y_728_);
lean_closure_set(v___f_737_, 3, v___y_729_);
lean_closure_set(v___f_737_, 4, v___y_730_);
lean_closure_set(v___f_737_, 5, v___y_731_);
v___x_738_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_725_, v___f_737_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
if (lean_obj_tag(v___x_738_) == 0)
{
return v___x_738_;
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_738_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_738_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___boxed(lean_object* v_mvarId_747_, lean_object* v_x_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v_mvarId_747_, v_x_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1(lean_object* v_00_u03b1_760_, lean_object* v_mvarId_761_, lean_object* v_x_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v_mvarId_761_, v_x_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___boxed(lean_object* v_00_u03b1_774_, lean_object* v_mvarId_775_, lean_object* v_x_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1(v_00_u03b1_774_, v_mvarId_775_, v_x_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(lean_object* v_e_788_){
_start:
{
if (lean_obj_tag(v_e_788_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_798_; 
v_a_790_ = lean_ctor_get(v_e_788_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v_e_788_);
if (v_isSharedCheck_798_ == 0)
{
v___x_792_ = v_e_788_;
v_isShared_793_ = v_isSharedCheck_798_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v_e_788_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_798_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_794_ = lean_mk_io_user_error(v_a_790_);
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
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
v_a_799_ = lean_ctor_get(v_e_788_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v_e_788_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v_e_788_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v_e_788_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
lean_ctor_set_tag(v___x_801_, 0);
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg___boxed(lean_object* v_e_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v_e_807_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2(lean_object* v_00_u03b1_810_, lean_object* v_e_811_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v_e_811_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___boxed(lean_object* v_00_u03b1_814_, lean_object* v_e_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2(v_00_u03b1_814_, v_e_815_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(lean_object* v_msg_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_ref_824_; lean_object* v___x_825_; lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_834_; 
v_ref_824_ = lean_ctor_get(v___y_821_, 2);
v___x_825_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v_msg_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
v_a_826_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_834_ == 0)
{
v___x_828_ = v___x_825_;
v_isShared_829_ = v_isSharedCheck_834_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_825_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_834_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_832_; 
lean_inc(v_ref_824_);
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v_ref_824_);
lean_ctor_set(v___x_830_, 1, v_a_826_);
if (v_isShared_829_ == 0)
{
lean_ctor_set_tag(v___x_828_, 1);
lean_ctor_set(v___x_828_, 0, v___x_830_);
v___x_832_ = v___x_828_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg___boxed(lean_object* v_msg_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(v_msg_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(lean_object* v_target_844_, lean_object* v_ctx_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_exprDef_856_; lean_object* v_certDef_857_; lean_object* v_reflectionDef_858_; lean_object* v_solver_859_; lean_object* v_lratPath_860_; lean_object* v_config_861_; lean_object* v_restrictedTypes_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_1025_; 
v_exprDef_856_ = lean_ctor_get(v_ctx_845_, 0);
v_certDef_857_ = lean_ctor_get(v_ctx_845_, 1);
v_reflectionDef_858_ = lean_ctor_get(v_ctx_845_, 2);
v_solver_859_ = lean_ctor_get(v_ctx_845_, 3);
v_lratPath_860_ = lean_ctor_get(v_ctx_845_, 4);
v_config_861_ = lean_ctor_get(v_ctx_845_, 5);
v_restrictedTypes_862_ = lean_ctor_get(v_ctx_845_, 6);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_ctx_845_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_864_ = v_ctx_845_;
v_isShared_865_ = v_isSharedCheck_1025_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_restrictedTypes_862_);
lean_inc(v_config_861_);
lean_inc(v_lratPath_860_);
lean_inc(v_solver_859_);
lean_inc(v_reflectionDef_858_);
lean_inc(v_certDef_857_);
lean_inc(v_exprDef_856_);
lean_dec(v_ctx_845_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_1025_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v_timeout_890_; uint8_t v_trimProofs_891_; uint8_t v_binaryProofs_892_; uint8_t v_acNf_893_; uint8_t v_andFlattening_894_; uint8_t v_embeddedConstraintSubst_895_; uint8_t v_structures_896_; uint8_t v_fixedInt_897_; uint8_t v_enums_898_; uint8_t v_graphviz_899_; lean_object* v_maxSteps_900_; uint8_t v_shortCircuit_901_; uint8_t v_solverMode_902_; uint8_t v_uf_903_; lean_object* v_cegarRounds_904_; uint8_t v_epr_905_; uint8_t v_eprSymBreak_906_; uint8_t v_eprProjections_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_1024_; 
v_timeout_890_ = lean_ctor_get(v_config_861_, 0);
v_trimProofs_891_ = lean_ctor_get_uint8(v_config_861_, sizeof(void*)*3);
v_binaryProofs_892_ = lean_ctor_get_uint8(v_config_861_, sizeof(void*)*3 + 1);
v_acNf_893_ = lean_ctor_get_uint8(v_config_861_, sizeof(void*)*3 + 2);
v_andFlattening_894_ = lean_ctor_get_uint8(v_config_861_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_895_ = lean_ctor_get_uint8(v_config_861_, sizeof(void*)*3 + 4);
v_structures_896_ = lean_ctor_get_uint8(v_config_861_, sizeof(void*)*3 + 5);
v_fixedInt_897_ = lean_ctor_get_uint8(v_config_861_, sizeof(void*)*3 + 6);
v_enums_898_ = lean_ctor_get_uint8(v_config_861_, sizeof(void*)*3 + 7);
v_graphviz_899_ = lean_ctor_get_uint8(v_config_861_, sizeof(void*)*3 + 8);
v_maxSteps_900_ = lean_ctor_get(v_config_861_, 1);
v_shortCircuit_901_ = lean_ctor_get_uint8(v_config_861_, sizeof(void*)*3 + 9);
v_solverMode_902_ = lean_ctor_get_uint8(v_config_861_, sizeof(void*)*3 + 10);
v_uf_903_ = lean_ctor_get_uint8(v_config_861_, sizeof(void*)*3 + 11);
v_cegarRounds_904_ = lean_ctor_get(v_config_861_, 2);
v_epr_905_ = lean_ctor_get_uint8(v_config_861_, sizeof(void*)*3 + 12);
v_eprSymBreak_906_ = lean_ctor_get_uint8(v_config_861_, sizeof(void*)*3 + 13);
v_eprProjections_907_ = lean_ctor_get_uint8(v_config_861_, sizeof(void*)*3 + 14);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_config_861_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_909_ = v_config_861_;
v_isShared_910_ = v_isSharedCheck_1024_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_cegarRounds_904_);
lean_inc(v_maxSteps_900_);
lean_inc(v_timeout_890_);
lean_dec(v_config_861_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_1024_;
goto v_resetjp_908_;
}
v___jp_866_:
{
lean_object* v___x_876_; 
v___x_876_ = l_System_FilePath_fileName(v_lratPath_860_);
if (lean_obj_tag(v___x_876_) == 1)
{
lean_object* v_val_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_887_; 
v_val_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_887_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_887_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_val_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_887_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_881_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__0));
if (v_isShared_880_ == 0)
{
v___x_883_ = v___x_879_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_val_877_);
v___x_883_ = v_reuseFailAlloc_886_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_881_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v___x_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
return v___x_885_;
}
}
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; 
lean_dec(v___x_876_);
v___x_888_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5, &l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5);
v___x_889_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(v___x_888_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
return v___x_889_;
}
}
v_resetjp_908_:
{
lean_object* v___x_911_; uint8_t v___x_912_; lean_object* v___x_914_; 
v___x_911_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_844_);
v___x_912_ = 0;
if (v_isShared_910_ == 0)
{
v___x_914_ = v___x_909_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 3, 15);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_timeout_890_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_maxSteps_900_);
lean_ctor_set(v_reuseFailAlloc_1023_, 2, v_cegarRounds_904_);
lean_ctor_set_uint8(v_reuseFailAlloc_1023_, sizeof(void*)*3 + 1, v_binaryProofs_892_);
lean_ctor_set_uint8(v_reuseFailAlloc_1023_, sizeof(void*)*3 + 2, v_acNf_893_);
lean_ctor_set_uint8(v_reuseFailAlloc_1023_, sizeof(void*)*3 + 3, v_andFlattening_894_);
lean_ctor_set_uint8(v_reuseFailAlloc_1023_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_895_);
lean_ctor_set_uint8(v_reuseFailAlloc_1023_, sizeof(void*)*3 + 5, v_structures_896_);
lean_ctor_set_uint8(v_reuseFailAlloc_1023_, sizeof(void*)*3 + 6, v_fixedInt_897_);
lean_ctor_set_uint8(v_reuseFailAlloc_1023_, sizeof(void*)*3 + 7, v_enums_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_1023_, sizeof(void*)*3 + 8, v_graphviz_899_);
lean_ctor_set_uint8(v_reuseFailAlloc_1023_, sizeof(void*)*3 + 9, v_shortCircuit_901_);
lean_ctor_set_uint8(v_reuseFailAlloc_1023_, sizeof(void*)*3 + 10, v_solverMode_902_);
lean_ctor_set_uint8(v_reuseFailAlloc_1023_, sizeof(void*)*3 + 11, v_uf_903_);
lean_ctor_set_uint8(v_reuseFailAlloc_1023_, sizeof(void*)*3 + 12, v_epr_905_);
lean_ctor_set_uint8(v_reuseFailAlloc_1023_, sizeof(void*)*3 + 13, v_eprSymBreak_906_);
lean_ctor_set_uint8(v_reuseFailAlloc_1023_, sizeof(void*)*3 + 14, v_eprProjections_907_);
v___x_914_ = v_reuseFailAlloc_1023_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_916_; 
lean_ctor_set_uint8(v___x_914_, sizeof(void*)*3, v___x_912_);
lean_inc_ref(v_lratPath_860_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 5, v___x_914_);
v___x_916_ = v___x_864_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_exprDef_856_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v_certDef_857_);
lean_ctor_set(v_reuseFailAlloc_1022_, 2, v_reflectionDef_858_);
lean_ctor_set(v_reuseFailAlloc_1022_, 3, v_solver_859_);
lean_ctor_set(v_reuseFailAlloc_1022_, 4, v_lratPath_860_);
lean_ctor_set(v_reuseFailAlloc_1022_, 5, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_1022_, 6, v_restrictedTypes_862_);
v___x_916_ = v_reuseFailAlloc_1022_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed), 12, 2);
lean_closure_set(v___x_917_, 0, v_target_844_);
lean_closure_set(v___x_917_, 1, v___x_916_);
v___x_918_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v___x_911_, v___x_917_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_1013_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_1013_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_1013_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v_lratCert_923_; 
v_lratCert_923_ = lean_ctor_get(v_a_919_, 1);
lean_inc(v_lratCert_923_);
if (lean_obj_tag(v_lratCert_923_) == 0)
{
lean_object* v_lemmas_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_935_; 
lean_dec_ref(v_lratPath_860_);
v_lemmas_924_ = lean_ctor_get(v_a_919_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v_a_919_);
if (v_isSharedCheck_935_ == 0)
{
lean_object* v_unused_936_; 
v_unused_936_ = lean_ctor_get(v_a_919_, 1);
lean_dec(v_unused_936_);
v___x_926_ = v_a_919_;
v_isShared_927_ = v_isSharedCheck_935_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_lemmas_924_);
lean_dec(v_a_919_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_935_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_928_ = lean_box(0);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 1, v___x_928_);
v___x_930_ = v___x_926_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_lemmas_924_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v___x_928_);
v___x_930_ = v_reuseFailAlloc_934_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
lean_object* v___x_932_; 
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_930_);
v___x_932_ = v___x_921_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_lemmas_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_1011_; 
v_lemmas_937_ = lean_ctor_get(v_a_919_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_a_919_);
if (v_isSharedCheck_1011_ == 0)
{
lean_object* v_unused_1012_; 
v_unused_1012_ = lean_ctor_get(v_a_919_, 1);
lean_dec(v_unused_1012_);
v___x_939_ = v_a_919_;
v_isShared_940_ = v_isSharedCheck_1011_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_lemmas_937_);
lean_dec(v_a_919_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_1011_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_1009_; 
v_isSharedCheck_1009_ = !lean_is_exclusive(v_lratCert_923_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; 
v_unused_1010_ = lean_ctor_get(v_lratCert_923_, 0);
lean_dec(v_unused_1010_);
v___x_942_ = v_lratCert_923_;
v_isShared_943_ = v_isSharedCheck_1009_;
goto v_resetjp_941_;
}
else
{
lean_dec(v_lratCert_923_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_1009_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_944_ = lean_array_get_size(v_lemmas_937_);
v___x_945_ = lean_unsigned_to_nat(0u);
v___x_946_ = lean_nat_dec_eq(v___x_944_, v___x_945_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; lean_object* v___x_949_; 
lean_del_object(v___x_942_);
lean_dec_ref(v_lratPath_860_);
v___x_947_ = lean_box(2);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_947_);
v___x_949_ = v___x_939_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_lemmas_937_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v___x_947_);
v___x_949_ = v_reuseFailAlloc_953_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_951_; 
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_949_);
v___x_951_ = v___x_921_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
else
{
lean_dec_ref(v_lemmas_937_);
lean_del_object(v___x_921_);
if (v_trimProofs_891_ == 0)
{
lean_del_object(v___x_942_);
lean_del_object(v___x_939_);
v___y_867_ = v_a_846_;
v___y_868_ = v_a_847_;
v___y_869_ = v_a_848_;
v___y_870_ = v_a_849_;
v___y_871_ = v_a_850_;
v___y_872_ = v_a_851_;
v___y_873_ = v_a_852_;
v___y_874_ = v_a_853_;
v___y_875_ = v_a_854_;
goto v___jp_866_;
}
else
{
lean_object* v_ref_954_; lean_object* v___x_955_; 
v_ref_954_ = lean_ctor_get(v_a_853_, 2);
v___x_955_ = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(v_lratPath_860_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
lean_dec_ref_known(v___x_955_, 1);
v___x_957_ = l_Lean_Meta_Tactic_BVDecide_LRAT_trim(v_a_956_);
lean_dec(v_a_956_);
v___x_958_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v___x_957_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_960_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref_known(v___x_958_, 1);
v___x_960_ = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(v_lratPath_860_, v_a_959_, v_binaryProofs_892_);
lean_dec(v_a_959_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_dec_ref_known(v___x_960_, 1);
lean_del_object(v___x_942_);
lean_del_object(v___x_939_);
v___y_867_ = v_a_846_;
v___y_868_ = v_a_847_;
v___y_869_ = v_a_848_;
v___y_870_ = v_a_849_;
v___y_871_ = v_a_850_;
v___y_872_ = v_a_851_;
v___y_873_ = v_a_852_;
v___y_874_ = v_a_853_;
v___y_875_ = v_a_854_;
goto v___jp_866_;
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_976_; 
lean_dec_ref(v_lratPath_860_);
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_976_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_976_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_976_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_965_; lean_object* v___x_967_; 
v___x_965_ = lean_io_error_to_string(v_a_961_);
if (v_isShared_943_ == 0)
{
lean_ctor_set_tag(v___x_942_, 3);
lean_ctor_set(v___x_942_, 0, v___x_965_);
v___x_967_ = v___x_942_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_965_);
v___x_967_ = v_reuseFailAlloc_975_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_968_ = l_Lean_MessageData_ofFormat(v___x_967_);
lean_inc(v_ref_954_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_968_);
lean_ctor_set(v___x_939_, 0, v_ref_954_);
v___x_970_ = v___x_939_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_ref_954_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v___x_968_);
v___x_970_ = v_reuseFailAlloc_974_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_972_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_970_);
v___x_972_ = v___x_963_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_992_; 
lean_dec_ref(v_lratPath_860_);
v_a_977_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_992_ == 0)
{
v___x_979_ = v___x_958_;
v_isShared_980_ = v_isSharedCheck_992_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_958_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_992_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_981_ = lean_io_error_to_string(v_a_977_);
if (v_isShared_943_ == 0)
{
lean_ctor_set_tag(v___x_942_, 3);
lean_ctor_set(v___x_942_, 0, v___x_981_);
v___x_983_ = v___x_942_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_981_);
v___x_983_ = v_reuseFailAlloc_991_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_984_; lean_object* v___x_986_; 
v___x_984_ = l_Lean_MessageData_ofFormat(v___x_983_);
lean_inc(v_ref_954_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_984_);
lean_ctor_set(v___x_939_, 0, v_ref_954_);
v___x_986_ = v___x_939_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_ref_954_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v___x_984_);
v___x_986_ = v_reuseFailAlloc_990_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_988_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_986_);
v___x_988_ = v___x_979_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1008_; 
lean_dec_ref(v_lratPath_860_);
v_a_993_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_995_ = v___x_955_;
v_isShared_996_ = v_isSharedCheck_1008_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_955_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1008_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_997_ = lean_io_error_to_string(v_a_993_);
if (v_isShared_943_ == 0)
{
lean_ctor_set_tag(v___x_942_, 3);
lean_ctor_set(v___x_942_, 0, v___x_997_);
v___x_999_ = v___x_942_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1007_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1000_; lean_object* v___x_1002_; 
v___x_1000_ = l_Lean_MessageData_ofFormat(v___x_999_);
lean_inc(v_ref_954_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_1000_);
lean_ctor_set(v___x_939_, 0, v_ref_954_);
v___x_1002_ = v___x_939_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_ref_954_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1004_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1002_);
v___x_1004_ = v___x_995_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
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
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec_ref(v_lratPath_860_);
v_a_1014_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_918_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_918_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___boxed(lean_object* v_target_1026_, lean_object* v_ctx_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(v_target_1026_, v_ctx_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
lean_dec(v_a_1028_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0(lean_object* v_00_u03b1_1039_, lean_object* v_msg_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(v_msg_1040_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___boxed(lean_object* v_00_u03b1_1052_, lean_object* v_msg_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0(v_00_u03b1_1052_, v_msg_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
return v_res_1064_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1065_ = lean_box(0);
v___x_1066_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v___x_1065_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg(){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0);
v___x_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___boxed(lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0(lean_object* v_00_u03b1_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___boxed(lean_object* v_00_u03b1_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0(v_00_u03b1_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(lean_object* v_snd_1095_, lean_object* v_ref_1096_, lean_object* v_a_x3f_1097_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_io_remove_file(v_snd_1095_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec(v_ref_1096_);
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1099_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1099_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1119_; 
v_a_1108_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1110_ = v___x_1099_;
v_isShared_1111_ = v_isSharedCheck_1119_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1099_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1119_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1117_; 
v___x_1112_ = lean_io_error_to_string(v_a_1108_);
v___x_1113_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
v___x_1114_ = l_Lean_MessageData_ofFormat(v___x_1113_);
v___x_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1115_, 0, v_ref_1096_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1115_);
v___x_1117_ = v___x_1110_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0___boxed(lean_object* v_snd_1120_, lean_object* v_ref_1121_, lean_object* v_a_x3f_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_1120_, v_ref_1121_, v_a_x3f_1122_);
lean_dec(v_a_x3f_1122_);
lean_dec_ref(v_snd_1120_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(lean_object* v_f_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v_ref_1135_; lean_object* v___x_1136_; 
v_ref_1135_ = lean_ctor_get(v___y_1132_, 2);
v___x_1136_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v_fst_1138_; lean_object* v_snd_1139_; lean_object* v_r_1140_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref_known(v___x_1136_, 1);
v_fst_1138_ = lean_ctor_get(v_a_1137_, 0);
lean_inc(v_fst_1138_);
v_snd_1139_ = lean_ctor_get(v_a_1137_, 1);
lean_inc_n(v_snd_1139_, 2);
lean_dec(v_a_1137_);
lean_inc(v___y_1133_);
lean_inc_ref(v___y_1132_);
lean_inc(v___y_1131_);
lean_inc_ref(v___y_1130_);
lean_inc(v___y_1129_);
lean_inc_ref(v___y_1128_);
lean_inc(v___y_1127_);
lean_inc_ref(v___y_1126_);
v_r_1140_ = lean_apply_11(v_f_1125_, v_fst_1138_, v_snd_1139_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, lean_box(0));
if (lean_obj_tag(v_r_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1165_; 
v_a_1141_ = lean_ctor_get(v_r_1140_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_r_1140_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1143_ = v_r_1140_;
v_isShared_1144_ = v_isSharedCheck_1165_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v_r_1140_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1165_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
lean_inc(v_a_1141_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set_tag(v___x_1143_, 1);
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1147_; 
lean_inc(v_ref_1135_);
v___x_1147_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_1139_, v_ref_1135_, v___x_1146_);
lean_dec_ref(v___x_1146_);
lean_dec(v_snd_1139_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; 
v_unused_1155_ = lean_ctor_get(v___x_1147_, 0);
lean_dec(v_unused_1155_);
v___x_1149_ = v___x_1147_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_dec(v___x_1147_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v_a_1141_);
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1141_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec(v_a_1141_);
v_a_1156_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1147_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1147_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v_a_1166_ = lean_ctor_get(v_r_1140_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v_r_1140_, 1);
v___x_1167_ = lean_box(0);
lean_inc(v_ref_1135_);
v___x_1168_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_1139_, v_ref_1135_, v___x_1167_);
lean_dec(v_snd_1139_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1175_ == 0)
{
lean_object* v_unused_1176_; 
v_unused_1176_ = lean_ctor_get(v___x_1168_, 0);
lean_dec(v_unused_1176_);
v___x_1170_ = v___x_1168_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_dec(v___x_1168_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
lean_ctor_set_tag(v___x_1170_, 1);
lean_ctor_set(v___x_1170_, 0, v_a_1166_);
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1166_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
lean_dec(v_a_1166_);
v_a_1177_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1168_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1168_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1196_; 
lean_dec_ref(v_f_1125_);
v_a_1185_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1187_ = v___x_1136_;
v_isShared_1188_ = v_isSharedCheck_1196_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1136_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1196_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1189_ = lean_io_error_to_string(v_a_1185_);
v___x_1190_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
v___x_1191_ = l_Lean_MessageData_ofFormat(v___x_1190_);
lean_inc(v_ref_1135_);
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v_ref_1135_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v___x_1192_);
v___x_1194_ = v___x_1187_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___boxed(lean_object* v_f_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(v_f_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1(lean_object* v_00_u03b1_1208_, lean_object* v_f_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(v_f_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___boxed(lean_object* v_00_u03b1_1220_, lean_object* v_f_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1(v_00_u03b1_1220_, v_f_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0(uint8_t v___x_1232_, lean_object* v___x_1233_, uint8_t v___x_1234_, lean_object* v___x_1235_, lean_object* v___x_1236_, lean_object* v___x_1237_, lean_object* v_a_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1240_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1249_);
lean_dec_ref_known(v___x_1248_, 1);
v___x_1250_ = lean_unsigned_to_nat(1024u);
v___x_1251_ = lean_unsigned_to_nat(9u);
v___x_1252_ = lean_unsigned_to_nat(5u);
v___x_1253_ = lean_unsigned_to_nat(8u);
v___x_1254_ = lean_unsigned_to_nat(10000u);
v___x_1255_ = lean_unsigned_to_nat(16u);
v___x_1256_ = lean_unsigned_to_nat(1048576u);
v___x_1257_ = lean_unsigned_to_nat(50u);
v___x_1258_ = lean_box(0);
lean_inc_n(v___x_1233_, 2);
v___x_1259_ = lean_alloc_ctor(0, 18, 35);
lean_ctor_set(v___x_1259_, 0, v___x_1250_);
lean_ctor_set(v___x_1259_, 1, v___x_1251_);
lean_ctor_set(v___x_1259_, 2, v___x_1252_);
lean_ctor_set(v___x_1259_, 3, v___x_1253_);
lean_ctor_set(v___x_1259_, 4, v___x_1253_);
lean_ctor_set(v___x_1259_, 5, v___x_1233_);
lean_ctor_set(v___x_1259_, 6, v___x_1233_);
lean_ctor_set(v___x_1259_, 7, v___x_1235_);
lean_ctor_set(v___x_1259_, 8, v___x_1236_);
lean_ctor_set(v___x_1259_, 9, v___x_1250_);
lean_ctor_set(v___x_1259_, 10, v___x_1254_);
lean_ctor_set(v___x_1259_, 11, v___x_1253_);
lean_ctor_set(v___x_1259_, 12, v___x_1255_);
lean_ctor_set(v___x_1259_, 13, v___x_1233_);
lean_ctor_set(v___x_1259_, 14, v___x_1256_);
lean_ctor_set(v___x_1259_, 15, v___x_1237_);
lean_ctor_set(v___x_1259_, 16, v___x_1257_);
lean_ctor_set(v___x_1259_, 17, v___x_1258_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18, v___x_1232_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 1, v___x_1232_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 2, v___x_1232_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 3, v___x_1232_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 4, v___x_1232_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 5, v___x_1234_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 6, v___x_1234_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 7, v___x_1234_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 8, v___x_1232_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 9, v___x_1232_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 10, v___x_1232_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 11, v___x_1234_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 12, v___x_1232_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 13, v___x_1234_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 14, v___x_1234_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 15, v___x_1234_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 16, v___x_1232_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 17, v___x_1234_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 18, v___x_1232_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 19, v___x_1234_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 20, v___x_1234_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 21, v___x_1234_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 22, v___x_1232_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 23, v___x_1234_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 24, v___x_1234_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 25, v___x_1234_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 26, v___x_1234_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 27, v___x_1234_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 28, v___x_1234_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 29, v___x_1234_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 30, v___x_1234_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 31, v___x_1234_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 32, v___x_1232_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 33, v___x_1234_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*18 + 34, v___x_1234_);
v___x_1260_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_1259_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___x_1260_, 1);
v___x_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1262_, 0, v_a_1249_);
v___x_1263_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed), 12, 2);
lean_closure_set(v___x_1263_, 0, v___x_1262_);
lean_closure_set(v___x_1263_, 1, v_a_1238_);
v___x_1264_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___x_1263_, v_a_1261_, v___x_1258_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
lean_dec_ref_known(v___x_1264_, 1);
v___x_1265_ = lean_box(0);
v___x_1266_ = lean_box(0);
v___x_1267_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1265_, v___y_1240_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v___x_1267_, 0);
lean_dec(v_unused_1275_);
v___x_1269_ = v___x_1267_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_dec(v___x_1267_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v___x_1266_);
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1266_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
else
{
return v___x_1267_;
}
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
v_a_1276_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1264_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1264_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec(v_a_1249_);
lean_dec_ref(v_a_1238_);
v_a_1284_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1260_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1260_);
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
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec_ref(v_a_1238_);
lean_dec(v___x_1237_);
lean_dec(v___x_1236_);
lean_dec(v___x_1235_);
lean_dec(v___x_1233_);
v_a_1292_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1248_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1248_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0___boxed(lean_object* v___x_1300_, lean_object* v___x_1301_, lean_object* v___x_1302_, lean_object* v___x_1303_, lean_object* v___x_1304_, lean_object* v___x_1305_, lean_object* v_a_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
uint8_t v___x_5648__boxed_1316_; uint8_t v___x_5650__boxed_1317_; lean_object* v_res_1318_; 
v___x_5648__boxed_1316_ = lean_unbox(v___x_1300_);
v___x_5650__boxed_1317_ = lean_unbox(v___x_1302_);
v_res_1318_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0(v___x_5648__boxed_1316_, v___x_1301_, v___x_5650__boxed_1317_, v___x_1303_, v___x_1304_, v___x_1305_, v_a_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1(lean_object* v_a_1319_, lean_object* v_a_1320_, uint8_t v___x_1321_, lean_object* v___x_1322_, uint8_t v___x_1323_, lean_object* v___x_1324_, lean_object* v___x_1325_, lean_object* v___x_1326_, lean_object* v_x_1327_, lean_object* v_lratFile_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new(v_lratFile_1328_, v_a_1319_, v_a_1320_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___f_1342_; lean_object* v___x_1343_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_a_1339_);
lean_dec_ref_known(v___x_1338_, 1);
v___x_1340_ = lean_box(v___x_1321_);
v___x_1341_ = lean_box(v___x_1323_);
v___f_1342_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0___boxed), 16, 7);
lean_closure_set(v___f_1342_, 0, v___x_1340_);
lean_closure_set(v___f_1342_, 1, v___x_1322_);
lean_closure_set(v___f_1342_, 2, v___x_1341_);
lean_closure_set(v___f_1342_, 3, v___x_1324_);
lean_closure_set(v___f_1342_, 4, v___x_1325_);
lean_closure_set(v___f_1342_, 5, v___x_1326_);
lean_closure_set(v___f_1342_, 6, v_a_1339_);
v___x_1343_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1342_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
return v___x_1343_;
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec(v___x_1326_);
lean_dec(v___x_1325_);
lean_dec(v___x_1324_);
lean_dec(v___x_1322_);
v_a_1344_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1338_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1338_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1___boxed(lean_object** _args){
lean_object* v_a_1352_ = _args[0];
lean_object* v_a_1353_ = _args[1];
lean_object* v___x_1354_ = _args[2];
lean_object* v___x_1355_ = _args[3];
lean_object* v___x_1356_ = _args[4];
lean_object* v___x_1357_ = _args[5];
lean_object* v___x_1358_ = _args[6];
lean_object* v___x_1359_ = _args[7];
lean_object* v_x_1360_ = _args[8];
lean_object* v_lratFile_1361_ = _args[9];
lean_object* v___y_1362_ = _args[10];
lean_object* v___y_1363_ = _args[11];
lean_object* v___y_1364_ = _args[12];
lean_object* v___y_1365_ = _args[13];
lean_object* v___y_1366_ = _args[14];
lean_object* v___y_1367_ = _args[15];
lean_object* v___y_1368_ = _args[16];
lean_object* v___y_1369_ = _args[17];
lean_object* v___y_1370_ = _args[18];
_start:
{
uint8_t v___x_5805__boxed_1371_; uint8_t v___x_5807__boxed_1372_; lean_object* v_res_1373_; 
v___x_5805__boxed_1371_ = lean_unbox(v___x_1354_);
v___x_5807__boxed_1372_ = lean_unbox(v___x_1356_);
v_res_1373_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1(v_a_1352_, v_a_1353_, v___x_5805__boxed_1371_, v___x_1355_, v___x_5807__boxed_1372_, v___x_1357_, v___x_1358_, v___x_1359_, v_x_1360_, v_lratFile_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v_x_1360_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide(lean_object* v_x_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_){
_start:
{
lean_object* v___x_1404_; uint8_t v___x_1405_; 
v___x_1404_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3));
lean_inc(v_x_1394_);
v___x_1405_ = l_Lean_Syntax_isOfKind(v_x_1394_, v___x_1404_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; 
lean_dec(v_x_1394_);
v___x_1406_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1406_;
}
else
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1407_ = lean_unsigned_to_nat(1u);
v___x_1408_ = l_Lean_Syntax_getArg(v_x_1394_, v___x_1407_);
v___x_1409_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_1408_);
v___x_1410_ = l_Lean_Syntax_isOfKind(v___x_1408_, v___x_1409_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; 
lean_dec(v___x_1408_);
lean_dec(v_x_1394_);
v___x_1411_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1411_;
}
else
{
lean_object* v___x_1412_; lean_object* v_types_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___x_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
v___x_1412_ = lean_unsigned_to_nat(0u);
v___x_1455_ = lean_unsigned_to_nat(2u);
v___x_1456_ = l_Lean_Syntax_getArg(v_x_1394_, v___x_1455_);
lean_dec(v_x_1394_);
v___x_1457_ = l_Lean_Syntax_isNone(v___x_1456_);
if (v___x_1457_ == 0)
{
uint8_t v___x_1458_; 
lean_inc(v___x_1456_);
v___x_1458_ = l_Lean_Syntax_matchesNull(v___x_1456_, v___x_1407_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; 
lean_dec(v___x_1456_);
lean_dec(v___x_1408_);
v___x_1459_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1459_;
}
else
{
lean_object* v_types_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
v_types_1460_ = l_Lean_Syntax_getArg(v___x_1456_, v___x_1412_);
lean_dec(v___x_1456_);
v___x_1461_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_types_1460_);
v___x_1462_ = l_Lean_Syntax_isOfKind(v_types_1460_, v___x_1461_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; 
lean_dec(v_types_1460_);
lean_dec(v___x_1408_);
v___x_1463_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1463_;
}
else
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1464_, 0, v_types_1460_);
v_types_1414_ = v___x_1464_;
v___y_1415_ = v_a_1395_;
v___y_1416_ = v_a_1396_;
v___y_1417_ = v_a_1397_;
v___y_1418_ = v_a_1398_;
v___y_1419_ = v_a_1399_;
v___y_1420_ = v_a_1400_;
v___y_1421_ = v_a_1401_;
v___y_1422_ = v_a_1402_;
goto v___jp_1413_;
}
}
}
else
{
lean_object* v___x_1465_; 
lean_dec(v___x_1456_);
v___x_1465_ = lean_box(0);
v_types_1414_ = v___x_1465_;
v___y_1415_ = v_a_1395_;
v___y_1416_ = v_a_1396_;
v___y_1417_ = v_a_1397_;
v___y_1418_ = v_a_1398_;
v___y_1419_ = v_a_1399_;
v___y_1420_ = v_a_1400_;
v___y_1421_ = v_a_1401_;
v___y_1422_ = v_a_1402_;
goto v___jp_1413_;
}
v___jp_1413_:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v___x_1424_; uint8_t v___x_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec_ref_known(v___x_1423_, 1);
v___x_1424_ = lean_unsigned_to_nat(10u);
v___x_1425_ = 0;
v___x_1426_ = lean_unsigned_to_nat(100000u);
v___x_1427_ = 0;
v___x_1428_ = lean_unsigned_to_nat(1000u);
v___x_1429_ = 1;
v___x_1430_ = lean_alloc_ctor(0, 3, 15);
lean_ctor_set(v___x_1430_, 0, v___x_1424_);
lean_ctor_set(v___x_1430_, 1, v___x_1426_);
lean_ctor_set(v___x_1430_, 2, v___x_1428_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*3, v___x_1410_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*3 + 1, v___x_1410_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*3 + 2, v___x_1425_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*3 + 3, v___x_1410_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*3 + 4, v___x_1410_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*3 + 5, v___x_1410_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*3 + 6, v___x_1410_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*3 + 7, v___x_1410_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*3 + 8, v___x_1425_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*3 + 9, v___x_1425_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*3 + 10, v___x_1427_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*3 + 11, v___x_1425_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*3 + 12, v___x_1425_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*3 + 13, v___x_1429_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*3 + 14, v___x_1410_);
v___x_1431_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_1408_, v___x_1430_, v___x_1410_, v___y_1415_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1433_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1431_, 1);
v___x_1433_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_types_1414_, v_a_1432_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___f_1437_; lean_object* v___x_1438_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___x_1433_, 1);
v___x_1435_ = lean_box(v___x_1425_);
v___x_1436_ = lean_box(v___x_1410_);
v___f_1437_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1___boxed), 19, 8);
lean_closure_set(v___f_1437_, 0, v_a_1432_);
lean_closure_set(v___f_1437_, 1, v_a_1434_);
lean_closure_set(v___f_1437_, 2, v___x_1435_);
lean_closure_set(v___f_1437_, 3, v___x_1428_);
lean_closure_set(v___f_1437_, 4, v___x_1436_);
lean_closure_set(v___f_1437_, 5, v___x_1412_);
lean_closure_set(v___f_1437_, 6, v___x_1426_);
lean_closure_set(v___f_1437_, 7, v___x_1424_);
v___x_1438_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(v___f_1437_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
return v___x_1438_;
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec(v_a_1432_);
v_a_1439_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1433_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1433_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec(v_types_1414_);
v_a_1447_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1431_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1431_);
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
lean_dec(v_types_1414_);
lean_dec(v___x_1408_);
return v___x_1423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___boxed(lean_object* v_x_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide(v_x_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_);
lean_dec(v_a_1474_);
lean_dec_ref(v_a_1473_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1(){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1486_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1487_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3));
v___x_1488_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2));
v___x_1489_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___boxed), 10, 0);
v___x_1490_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1486_, v___x_1487_, v___x_1488_, v___x_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___boxed(lean_object* v_a_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1();
return v_res_1492_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Array_mkArray0___redArg();
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0(uint8_t v___x_1500_, lean_object* v___x_1501_, lean_object* v___x_1502_, lean_object* v___x_1503_, lean_object* v_a_1504_, lean_object* v_final_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_ref_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_ref_1511_ = lean_ctor_get(v___y_1508_, 2);
v___x_1512_ = l_Lean_SourceInfo_fromRef(v_ref_1511_, v___x_1500_);
v___x_1513_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__0));
lean_inc_ref(v___x_1503_);
lean_inc_ref(v___x_1502_);
lean_inc_ref(v___x_1501_);
v___x_1514_ = l_Lean_Name_mkStr4(v___x_1501_, v___x_1502_, v___x_1503_, v___x_1513_);
v___x_1515_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__1));
v___x_1516_ = l_Lean_Name_mkStr4(v___x_1501_, v___x_1502_, v___x_1503_, v___x_1515_);
v___x_1517_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3));
v___x_1518_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4);
v___x_1519_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5));
v___x_1520_ = lean_array_push(v_a_1504_, v_final_1505_);
v___x_1521_ = l_Lean_Syntax_SepArray_ofElems(v___x_1519_, v___x_1520_);
lean_dec_ref(v___x_1520_);
v___x_1522_ = l_Array_append___redArg(v___x_1518_, v___x_1521_);
lean_dec_ref(v___x_1521_);
lean_inc_n(v___x_1512_, 2);
v___x_1523_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1512_);
lean_ctor_set(v___x_1523_, 1, v___x_1517_);
lean_ctor_set(v___x_1523_, 2, v___x_1522_);
v___x_1524_ = l_Lean_Syntax_node1(v___x_1512_, v___x_1516_, v___x_1523_);
v___x_1525_ = l_Lean_Syntax_node1(v___x_1512_, v___x_1514_, v___x_1524_);
v___x_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___boxed(lean_object* v___x_1527_, lean_object* v___x_1528_, lean_object* v___x_1529_, lean_object* v___x_1530_, lean_object* v_a_1531_, lean_object* v_final_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
uint8_t v___x_54132__boxed_1538_; lean_object* v_res_1539_; 
v___x_54132__boxed_1538_ = lean_unbox(v___x_1527_);
v_res_1539_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0(v___x_54132__boxed_1538_, v___x_1528_, v___x_1529_, v___x_1530_, v_a_1531_, v_final_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
return v_res_1539_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__14(void){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5));
v___x_1576_ = l_String_toRawSubstring_x27(v___x_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg(size_t v_sz_1633_, size_t v_i_1634_, lean_object* v_bs_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
uint8_t v___x_1641_; 
v___x_1641_ = lean_usize_dec_lt(v_i_1634_, v_sz_1633_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1642_; 
v___x_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1642_, 0, v_bs_1635_);
return v___x_1642_;
}
else
{
lean_object* v_v_1643_; lean_object* v_hyp_1644_; lean_object* v_tacticProof_1645_; lean_object* v_type_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1718_; 
v_v_1643_ = lean_array_uget_borrowed(v_bs_1635_, v_i_1634_);
v_hyp_1644_ = lean_ctor_get(v_v_1643_, 0);
lean_inc_ref(v_hyp_1644_);
v_tacticProof_1645_ = lean_ctor_get(v_v_1643_, 1);
lean_inc_ref(v_tacticProof_1645_);
v_type_1646_ = lean_ctor_get(v_hyp_1644_, 1);
v_isSharedCheck_1718_ = !lean_is_exclusive(v_hyp_1644_);
if (v_isSharedCheck_1718_ == 0)
{
lean_object* v_unused_1719_; lean_object* v_unused_1720_; lean_object* v_unused_1721_; 
v_unused_1719_ = lean_ctor_get(v_hyp_1644_, 3);
lean_dec(v_unused_1719_);
v_unused_1720_ = lean_ctor_get(v_hyp_1644_, 2);
lean_dec(v_unused_1720_);
v_unused_1721_ = lean_ctor_get(v_hyp_1644_, 0);
lean_dec(v_unused_1721_);
v___x_1648_ = v_hyp_1644_;
v_isShared_1649_ = v_isSharedCheck_1718_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_type_1646_);
lean_dec(v_hyp_1644_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1718_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v_bs_x27_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1650_ = lean_unsigned_to_nat(0u);
v_bs_x27_1651_ = lean_array_uset(v_bs_1635_, v_i_1634_, v___x_1650_);
v___x_1652_ = lean_box(1);
v___x_1653_ = l_Lean_PrettyPrinter_delab(v_type_1646_, v___x_1652_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1655_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
lean_dec_ref_known(v___x_1653_, 1);
lean_inc(v___y_1639_);
lean_inc_ref(v___y_1638_);
lean_inc(v___y_1637_);
lean_inc_ref(v___y_1636_);
v___x_1655_ = lean_apply_5(v_tacticProof_1645_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, lean_box(0));
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_toCold_1656_; lean_object* v_a_1657_; lean_object* v_ref_1658_; lean_object* v_quotContext_1659_; lean_object* v_currMacroScope_1660_; uint8_t v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1680_; 
v_toCold_1656_ = lean_ctor_get(v___y_1638_, 0);
v_a_1657_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1655_, 1);
v_ref_1658_ = lean_ctor_get(v___y_1638_, 2);
v_quotContext_1659_ = lean_ctor_get(v_toCold_1656_, 8);
v_currMacroScope_1660_ = lean_ctor_get(v_toCold_1656_, 9);
v___x_1661_ = 0;
v___x_1662_ = l_Lean_SourceInfo_fromRef(v_ref_1658_, v___x_1661_);
v___x_1663_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__1));
v___x_1664_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__2));
lean_inc_n(v___x_1662_, 4);
v___x_1665_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1662_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
v___x_1666_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__5));
v___x_1667_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3));
v___x_1668_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4);
v___x_1669_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1662_);
lean_ctor_set(v___x_1669_, 1, v___x_1667_);
lean_ctor_set(v___x_1669_, 2, v___x_1668_);
lean_inc_ref(v___x_1669_);
v___x_1670_ = l_Lean_Syntax_node1(v___x_1662_, v___x_1666_, v___x_1669_);
v___x_1671_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__7));
v___x_1672_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__9));
v___x_1673_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__11));
v___x_1674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__13));
v___x_1675_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__14);
v___x_1676_ = lean_box(0);
lean_inc(v_currMacroScope_1660_);
lean_inc(v_quotContext_1659_);
v___x_1677_ = l_Lean_addMacroScope(v_quotContext_1659_, v___x_1676_, v_currMacroScope_1660_);
v___x_1678_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__28));
if (v_isShared_1649_ == 0)
{
lean_ctor_set_tag(v___x_1648_, 3);
lean_ctor_set(v___x_1648_, 3, v___x_1678_);
lean_ctor_set(v___x_1648_, 2, v___x_1677_);
lean_ctor_set(v___x_1648_, 1, v___x_1675_);
lean_ctor_set(v___x_1648_, 0, v___x_1662_);
v___x_1680_ = v___x_1648_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1662_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v___x_1675_);
lean_ctor_set(v_reuseFailAlloc_1701_, 2, v___x_1677_);
lean_ctor_set(v_reuseFailAlloc_1701_, 3, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; size_t v___x_1697_; size_t v___x_1698_; lean_object* v___x_1699_; 
lean_inc_n(v___x_1662_, 10);
v___x_1681_ = l_Lean_Syntax_node1(v___x_1662_, v___x_1674_, v___x_1680_);
v___x_1682_ = l_Lean_Syntax_node1(v___x_1662_, v___x_1673_, v___x_1681_);
v___x_1683_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__30));
v___x_1684_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__31));
v___x_1685_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1662_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
v___x_1686_ = l_Lean_Syntax_node2(v___x_1662_, v___x_1683_, v___x_1685_, v_a_1654_);
v___x_1687_ = l_Lean_Syntax_node1(v___x_1662_, v___x_1667_, v___x_1686_);
v___x_1688_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__32));
v___x_1689_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1662_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
v___x_1690_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__34));
v___x_1691_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__35));
v___x_1692_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1662_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
v___x_1693_ = l_Lean_Syntax_node2(v___x_1662_, v___x_1690_, v___x_1692_, v_a_1657_);
v___x_1694_ = l_Lean_Syntax_node5(v___x_1662_, v___x_1672_, v___x_1682_, v___x_1669_, v___x_1687_, v___x_1689_, v___x_1693_);
v___x_1695_ = l_Lean_Syntax_node1(v___x_1662_, v___x_1671_, v___x_1694_);
v___x_1696_ = l_Lean_Syntax_node3(v___x_1662_, v___x_1663_, v___x_1665_, v___x_1670_, v___x_1695_);
v___x_1697_ = ((size_t)1ULL);
v___x_1698_ = lean_usize_add(v_i_1634_, v___x_1697_);
v___x_1699_ = lean_array_uset(v_bs_x27_1651_, v_i_1634_, v___x_1696_);
v_i_1634_ = v___x_1698_;
v_bs_1635_ = v___x_1699_;
goto _start;
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec(v_a_1654_);
lean_dec_ref(v_bs_x27_1651_);
lean_del_object(v___x_1648_);
v_a_1702_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1655_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1655_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_dec_ref(v_bs_x27_1651_);
lean_del_object(v___x_1648_);
lean_dec_ref(v_tacticProof_1645_);
v_a_1710_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1653_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1653_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___boxed(lean_object* v_sz_1722_, lean_object* v_i_1723_, lean_object* v_bs_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
size_t v_sz_boxed_1730_; size_t v_i_boxed_1731_; lean_object* v_res_1732_; 
v_sz_boxed_1730_ = lean_unbox_usize(v_sz_1722_);
lean_dec(v_sz_1722_);
v_i_boxed_1731_ = lean_unbox_usize(v_i_1723_);
lean_dec(v_i_1723_);
v_res_1732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg(v_sz_boxed_1730_, v_i_boxed_1731_, v_bs_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0(size_t v_sz_1733_, size_t v_i_1734_, lean_object* v_bs_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg(v_sz_1733_, v_i_1734_, v_bs_1735_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___boxed(lean_object* v_sz_1747_, lean_object* v_i_1748_, lean_object* v_bs_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
size_t v_sz_boxed_1760_; size_t v_i_boxed_1761_; lean_object* v_res_1762_; 
v_sz_boxed_1760_ = lean_unbox_usize(v_sz_1747_);
lean_dec(v_sz_1747_);
v_i_boxed_1761_ = lean_unbox_usize(v_i_1748_);
lean_dec(v_i_1748_);
v_res_1762_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0(v_sz_boxed_1760_, v_i_boxed_1761_, v_bs_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1(lean_object* v___x_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, uint8_t v___x_1774_, lean_object* v___x_1775_, lean_object* v___x_1776_, lean_object* v___x_1777_, lean_object* v___x_1778_, lean_object* v_tk_1779_, lean_object* v_typesStx_1780_, lean_object* v___x_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(v___x_1771_, v_a_1772_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; lean_object* v_lemmas_1794_; lean_object* v_action_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1926_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1793_);
lean_dec_ref_known(v___x_1792_, 1);
v_lemmas_1794_ = lean_ctor_get(v_a_1793_, 0);
v_action_1795_ = lean_ctor_get(v_a_1793_, 1);
v_isSharedCheck_1926_ = !lean_is_exclusive(v_a_1793_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1797_ = v_a_1793_;
v_isShared_1798_ = v_isSharedCheck_1926_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_action_1795_);
lean_inc(v_lemmas_1794_);
lean_dec(v_a_1793_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1926_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
size_t v_sz_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v_sz_1799_ = lean_array_size(v_lemmas_1794_);
v___x_1800_ = lean_box_usize(v_sz_1799_);
v___x_1801_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___boxed__const__1));
v___x_1802_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___boxed), 13, 3);
lean_closure_set(v___x_1802_, 0, v___x_1800_);
lean_closure_set(v___x_1802_, 1, v___x_1801_);
lean_closure_set(v___x_1802_, 2, v_lemmas_1794_);
v___x_1803_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v_a_1773_, v___x_1802_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
if (lean_obj_tag(v___x_1803_) == 0)
{
switch(lean_obj_tag(v_action_1795_))
{
case 0:
{
lean_object* v_a_1804_; lean_object* v_ref_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1811_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_a_1804_);
lean_dec_ref_known(v___x_1803_, 1);
v_ref_1805_ = lean_ctor_get(v___y_1789_, 2);
v___x_1806_ = l_Lean_SourceInfo_fromRef(v_ref_1805_, v___x_1774_);
v___x_1807_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__0));
lean_inc_ref(v___x_1777_);
lean_inc_ref(v___x_1776_);
lean_inc_ref(v___x_1775_);
v___x_1808_ = l_Lean_Name_mkStr4(v___x_1775_, v___x_1776_, v___x_1777_, v___x_1807_);
v___x_1809_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__1));
lean_inc(v___x_1806_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set_tag(v___x_1797_, 2);
lean_ctor_set(v___x_1797_, 1, v___x_1809_);
lean_ctor_set(v___x_1797_, 0, v___x_1806_);
v___x_1811_ = v___x_1797_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1806_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___y_1815_; 
v___x_1812_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3));
v___x_1813_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4);
if (lean_obj_tag(v_typesStx_1780_) == 1)
{
lean_object* v_val_1837_; lean_object* v___x_1838_; 
v_val_1837_ = lean_ctor_get(v_typesStx_1780_, 0);
lean_inc(v_val_1837_);
lean_dec_ref_known(v_typesStx_1780_, 1);
v___x_1838_ = l_Array_mkArray1___redArg(v_val_1837_);
v___y_1815_ = v___x_1838_;
goto v___jp_1814_;
}
else
{
lean_object* v___x_1839_; 
lean_dec(v_typesStx_1780_);
v___x_1839_ = lean_mk_empty_array_with_capacity(v___x_1781_);
v___y_1815_ = v___x_1839_;
goto v___jp_1814_;
}
v___jp_1814_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1836_; 
v___x_1816_ = l_Array_append___redArg(v___x_1813_, v___y_1815_);
lean_dec_ref(v___y_1815_);
lean_inc(v___x_1806_);
v___x_1817_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1806_);
lean_ctor_set(v___x_1817_, 1, v___x_1812_);
lean_ctor_set(v___x_1817_, 2, v___x_1816_);
v___x_1818_ = l_Lean_Syntax_node3(v___x_1806_, v___x_1808_, v___x_1811_, v___x_1778_, v___x_1817_);
lean_inc_ref(v___x_1777_);
lean_inc_ref(v___x_1776_);
lean_inc_ref(v___x_1775_);
v___x_1819_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0(v___x_1774_, v___x_1775_, v___x_1776_, v___x_1777_, v_a_1804_, v___x_1818_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1822_ = v___x_1819_;
v_isShared_1823_ = v_isSharedCheck_1836_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1819_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1836_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1830_; 
v___x_1824_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__0));
v___x_1825_ = l_Lean_Name_mkStr4(v___x_1775_, v___x_1776_, v___x_1777_, v___x_1824_);
v___x_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
lean_ctor_set(v___x_1826_, 1, v_a_1820_);
v___x_1827_ = lean_box(0);
v___x_1828_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1826_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
lean_ctor_set(v___x_1828_, 2, v___x_1827_);
lean_ctor_set(v___x_1828_, 3, v___x_1827_);
lean_ctor_set(v___x_1828_, 4, v___x_1827_);
lean_ctor_set(v___x_1828_, 5, v___x_1827_);
lean_inc(v_ref_1805_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set_tag(v___x_1822_, 1);
lean_ctor_set(v___x_1822_, 0, v_ref_1805_);
v___x_1830_ = v___x_1822_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_ref_1805_);
v___x_1830_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1831_; uint8_t v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1831_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__2));
v___x_1832_ = 4;
v___x_1833_ = l_Lean_MessageData_nil;
v___x_1834_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1779_, v___x_1828_, v___x_1830_, v___x_1831_, v___x_1827_, v___x_1832_, v___x_1833_, v___y_1789_, v___y_1790_);
return v___x_1834_;
}
}
}
}
}
case 1:
{
lean_object* v_a_1841_; lean_object* v_path_1842_; lean_object* v_ref_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1849_; 
v_a_1841_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_a_1841_);
lean_dec_ref_known(v___x_1803_, 1);
v_path_1842_ = lean_ctor_get(v_action_1795_, 0);
lean_inc_ref(v_path_1842_);
lean_dec_ref_known(v_action_1795_, 1);
v_ref_1843_ = lean_ctor_get(v___y_1789_, 2);
v___x_1844_ = l_Lean_SourceInfo_fromRef(v_ref_1843_, v___x_1774_);
v___x_1845_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__3));
lean_inc_ref(v___x_1777_);
lean_inc_ref(v___x_1776_);
lean_inc_ref(v___x_1775_);
v___x_1846_ = l_Lean_Name_mkStr4(v___x_1775_, v___x_1776_, v___x_1777_, v___x_1845_);
v___x_1847_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__4));
lean_inc(v___x_1844_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set_tag(v___x_1797_, 2);
lean_ctor_set(v___x_1797_, 1, v___x_1847_);
lean_ctor_set(v___x_1797_, 0, v___x_1844_);
v___x_1849_ = v___x_1797_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1844_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___y_1853_; 
v___x_1850_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3));
v___x_1851_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4);
if (lean_obj_tag(v_typesStx_1780_) == 1)
{
lean_object* v_val_1877_; lean_object* v___x_1878_; 
v_val_1877_ = lean_ctor_get(v_typesStx_1780_, 0);
lean_inc(v_val_1877_);
lean_dec_ref_known(v_typesStx_1780_, 1);
v___x_1878_ = l_Array_mkArray1___redArg(v_val_1877_);
v___y_1853_ = v___x_1878_;
goto v___jp_1852_;
}
else
{
lean_object* v___x_1879_; 
lean_dec(v_typesStx_1780_);
v___x_1879_ = lean_mk_empty_array_with_capacity(v___x_1781_);
v___y_1853_ = v___x_1879_;
goto v___jp_1852_;
}
v___jp_1852_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1876_; 
v___x_1854_ = l_Array_append___redArg(v___x_1851_, v___y_1853_);
lean_dec_ref(v___y_1853_);
lean_inc(v___x_1844_);
v___x_1855_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1844_);
lean_ctor_set(v___x_1855_, 1, v___x_1850_);
lean_ctor_set(v___x_1855_, 2, v___x_1854_);
v___x_1856_ = lean_box(2);
v___x_1857_ = l_Lean_Syntax_mkStrLit(v_path_1842_, v___x_1856_);
v___x_1858_ = l_Lean_Syntax_node4(v___x_1844_, v___x_1846_, v___x_1849_, v___x_1778_, v___x_1855_, v___x_1857_);
lean_inc_ref(v___x_1777_);
lean_inc_ref(v___x_1776_);
lean_inc_ref(v___x_1775_);
v___x_1859_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0(v___x_1774_, v___x_1775_, v___x_1776_, v___x_1777_, v_a_1841_, v___x_1858_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1876_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1876_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1870_; 
v___x_1864_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__0));
v___x_1865_ = l_Lean_Name_mkStr4(v___x_1775_, v___x_1776_, v___x_1777_, v___x_1864_);
v___x_1866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1865_);
lean_ctor_set(v___x_1866_, 1, v_a_1860_);
v___x_1867_ = lean_box(0);
v___x_1868_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1866_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
lean_ctor_set(v___x_1868_, 2, v___x_1867_);
lean_ctor_set(v___x_1868_, 3, v___x_1867_);
lean_ctor_set(v___x_1868_, 4, v___x_1867_);
lean_ctor_set(v___x_1868_, 5, v___x_1867_);
lean_inc(v_ref_1843_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set_tag(v___x_1862_, 1);
lean_ctor_set(v___x_1862_, 0, v_ref_1843_);
v___x_1870_ = v___x_1862_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_ref_1843_);
v___x_1870_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1871_; uint8_t v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1871_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__2));
v___x_1872_ = 4;
v___x_1873_ = l_Lean_MessageData_nil;
v___x_1874_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1779_, v___x_1868_, v___x_1870_, v___x_1871_, v___x_1867_, v___x_1872_, v___x_1873_, v___y_1789_, v___y_1790_);
return v___x_1874_;
}
}
}
}
}
default: 
{
lean_object* v_a_1881_; lean_object* v_ref_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1888_; 
v_a_1881_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1803_, 1);
v_ref_1882_ = lean_ctor_get(v___y_1789_, 2);
v___x_1883_ = l_Lean_SourceInfo_fromRef(v_ref_1882_, v___x_1774_);
v___x_1884_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__2));
lean_inc_ref(v___x_1777_);
lean_inc_ref(v___x_1776_);
lean_inc_ref(v___x_1775_);
v___x_1885_ = l_Lean_Name_mkStr4(v___x_1775_, v___x_1776_, v___x_1777_, v___x_1884_);
v___x_1886_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__5));
lean_inc(v___x_1883_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set_tag(v___x_1797_, 2);
lean_ctor_set(v___x_1797_, 1, v___x_1886_);
lean_ctor_set(v___x_1797_, 0, v___x_1883_);
v___x_1888_ = v___x_1797_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1917_, 1, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___y_1892_; 
v___x_1889_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3));
v___x_1890_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4);
if (lean_obj_tag(v_typesStx_1780_) == 1)
{
lean_object* v_val_1914_; lean_object* v___x_1915_; 
v_val_1914_ = lean_ctor_get(v_typesStx_1780_, 0);
lean_inc(v_val_1914_);
lean_dec_ref_known(v_typesStx_1780_, 1);
v___x_1915_ = l_Array_mkArray1___redArg(v_val_1914_);
v___y_1892_ = v___x_1915_;
goto v___jp_1891_;
}
else
{
lean_object* v___x_1916_; 
lean_dec(v_typesStx_1780_);
v___x_1916_ = lean_mk_empty_array_with_capacity(v___x_1781_);
v___y_1892_ = v___x_1916_;
goto v___jp_1891_;
}
v___jp_1891_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1913_; 
v___x_1893_ = l_Array_append___redArg(v___x_1890_, v___y_1892_);
lean_dec_ref(v___y_1892_);
lean_inc(v___x_1883_);
v___x_1894_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1883_);
lean_ctor_set(v___x_1894_, 1, v___x_1889_);
lean_ctor_set(v___x_1894_, 2, v___x_1893_);
v___x_1895_ = l_Lean_Syntax_node3(v___x_1883_, v___x_1885_, v___x_1888_, v___x_1778_, v___x_1894_);
lean_inc_ref(v___x_1777_);
lean_inc_ref(v___x_1776_);
lean_inc_ref(v___x_1775_);
v___x_1896_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0(v___x_1774_, v___x_1775_, v___x_1776_, v___x_1777_, v_a_1881_, v___x_1895_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1899_ = v___x_1896_;
v_isShared_1900_ = v_isSharedCheck_1913_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1896_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1913_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1901_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__0));
v___x_1902_ = l_Lean_Name_mkStr4(v___x_1775_, v___x_1776_, v___x_1777_, v___x_1901_);
v___x_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
lean_ctor_set(v___x_1903_, 1, v_a_1897_);
v___x_1904_ = lean_box(0);
v___x_1905_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
lean_ctor_set(v___x_1905_, 2, v___x_1904_);
lean_ctor_set(v___x_1905_, 3, v___x_1904_);
lean_ctor_set(v___x_1905_, 4, v___x_1904_);
lean_ctor_set(v___x_1905_, 5, v___x_1904_);
lean_inc(v_ref_1882_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set_tag(v___x_1899_, 1);
lean_ctor_set(v___x_1899_, 0, v_ref_1882_);
v___x_1907_ = v___x_1899_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_ref_1882_);
v___x_1907_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1908_; uint8_t v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1908_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__2));
v___x_1909_ = 4;
v___x_1910_ = l_Lean_MessageData_nil;
v___x_1911_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1779_, v___x_1905_, v___x_1907_, v___x_1908_, v___x_1904_, v___x_1909_, v___x_1910_, v___y_1789_, v___y_1790_);
return v___x_1911_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
lean_del_object(v___x_1797_);
lean_dec(v_action_1795_);
lean_dec(v_typesStx_1780_);
lean_dec(v_tk_1779_);
lean_dec(v___x_1778_);
lean_dec_ref(v___x_1777_);
lean_dec_ref(v___x_1776_);
lean_dec_ref(v___x_1775_);
v_a_1918_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1803_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1803_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
lean_dec(v_typesStx_1780_);
lean_dec(v_tk_1779_);
lean_dec(v___x_1778_);
lean_dec_ref(v___x_1777_);
lean_dec_ref(v___x_1776_);
lean_dec_ref(v___x_1775_);
lean_dec(v_a_1773_);
v_a_1927_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1792_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1792_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___boxed(lean_object** _args){
lean_object* v___x_1935_ = _args[0];
lean_object* v_a_1936_ = _args[1];
lean_object* v_a_1937_ = _args[2];
lean_object* v___x_1938_ = _args[3];
lean_object* v___x_1939_ = _args[4];
lean_object* v___x_1940_ = _args[5];
lean_object* v___x_1941_ = _args[6];
lean_object* v___x_1942_ = _args[7];
lean_object* v_tk_1943_ = _args[8];
lean_object* v_typesStx_1944_ = _args[9];
lean_object* v___x_1945_ = _args[10];
lean_object* v___y_1946_ = _args[11];
lean_object* v___y_1947_ = _args[12];
lean_object* v___y_1948_ = _args[13];
lean_object* v___y_1949_ = _args[14];
lean_object* v___y_1950_ = _args[15];
lean_object* v___y_1951_ = _args[16];
lean_object* v___y_1952_ = _args[17];
lean_object* v___y_1953_ = _args[18];
lean_object* v___y_1954_ = _args[19];
lean_object* v___y_1955_ = _args[20];
_start:
{
uint8_t v___x_54712__boxed_1956_; lean_object* v_res_1957_; 
v___x_54712__boxed_1956_ = lean_unbox(v___x_1938_);
v_res_1957_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1(v___x_1935_, v_a_1936_, v_a_1937_, v___x_54712__boxed_1956_, v___x_1939_, v___x_1940_, v___x_1941_, v___x_1942_, v_tk_1943_, v_typesStx_1944_, v___x_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec(v___x_1945_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic(lean_object* v_x_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v___x_1974_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0));
v___x_1975_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1));
v___x_1976_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1));
v___x_1977_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__1));
lean_inc(v_x_1964_);
v___x_1978_ = l_Lean_Syntax_isOfKind(v_x_1964_, v___x_1977_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; 
lean_dec(v_x_1964_);
v___x_1979_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1979_;
}
else
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; 
v___x_1980_ = lean_unsigned_to_nat(1u);
v___x_1981_ = l_Lean_Syntax_getArg(v_x_1964_, v___x_1980_);
v___x_1982_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_1981_);
v___x_1983_ = l_Lean_Syntax_isOfKind(v___x_1981_, v___x_1982_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; 
lean_dec(v___x_1981_);
lean_dec(v_x_1964_);
v___x_1984_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1984_;
}
else
{
lean_object* v___x_1985_; lean_object* v_tk_1986_; lean_object* v_typesStx_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___x_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; 
v___x_1985_ = lean_unsigned_to_nat(0u);
v_tk_1986_ = l_Lean_Syntax_getArg(v_x_1964_, v___x_1985_);
v___x_2076_ = lean_unsigned_to_nat(2u);
v___x_2077_ = l_Lean_Syntax_getArg(v_x_1964_, v___x_2076_);
lean_dec(v_x_1964_);
v___x_2078_ = l_Lean_Syntax_isNone(v___x_2077_);
if (v___x_2078_ == 0)
{
uint8_t v___x_2079_; 
lean_inc(v___x_2077_);
v___x_2079_ = l_Lean_Syntax_matchesNull(v___x_2077_, v___x_1980_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2080_; 
lean_dec(v___x_2077_);
lean_dec(v_tk_1986_);
lean_dec(v___x_1981_);
v___x_2080_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2080_;
}
else
{
lean_object* v_typesStx_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
v_typesStx_2081_ = l_Lean_Syntax_getArg(v___x_2077_, v___x_1985_);
lean_dec(v___x_2077_);
v___x_2082_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_typesStx_2081_);
v___x_2083_ = l_Lean_Syntax_isOfKind(v_typesStx_2081_, v___x_2082_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; 
lean_dec(v_typesStx_2081_);
lean_dec(v_tk_1986_);
lean_dec(v___x_1981_);
v___x_2084_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2084_;
}
else
{
lean_object* v___x_2085_; 
v___x_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2085_, 0, v_typesStx_2081_);
v_typesStx_1988_ = v___x_2085_;
v___y_1989_ = v_a_1965_;
v___y_1990_ = v_a_1966_;
v___y_1991_ = v_a_1967_;
v___y_1992_ = v_a_1968_;
v___y_1993_ = v_a_1969_;
v___y_1994_ = v_a_1970_;
v___y_1995_ = v_a_1971_;
v___y_1996_ = v_a_1972_;
goto v___jp_1987_;
}
}
}
else
{
lean_object* v___x_2086_; 
lean_dec(v___x_2077_);
v___x_2086_ = lean_box(0);
v_typesStx_1988_ = v___x_2086_;
v___y_1989_ = v_a_1965_;
v___y_1990_ = v_a_1966_;
v___y_1991_ = v_a_1967_;
v___y_1992_ = v_a_1968_;
v___y_1993_ = v_a_1969_;
v___y_1994_ = v_a_1970_;
v___y_1995_ = v_a_1971_;
v___y_1996_ = v_a_1972_;
goto v___jp_1987_;
}
v___jp_1987_:
{
lean_object* v___x_1997_; 
v___x_1997_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2074_; 
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2074_ == 0)
{
lean_object* v_unused_2075_; 
v_unused_2075_ = lean_ctor_get(v___x_1997_, 0);
lean_dec(v_unused_2075_);
v___x_1999_ = v___x_1997_;
v_isShared_2000_ = v_isSharedCheck_2074_;
goto v_resetjp_1998_;
}
else
{
lean_dec(v___x_1997_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2074_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2001_; uint8_t v___x_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2001_ = lean_unsigned_to_nat(10u);
v___x_2002_ = 0;
v___x_2003_ = lean_unsigned_to_nat(100000u);
v___x_2004_ = 0;
v___x_2005_ = lean_unsigned_to_nat(1000u);
v___x_2006_ = 1;
v___x_2007_ = lean_alloc_ctor(0, 3, 15);
lean_ctor_set(v___x_2007_, 0, v___x_2001_);
lean_ctor_set(v___x_2007_, 1, v___x_2003_);
lean_ctor_set(v___x_2007_, 2, v___x_2005_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*3, v___x_1983_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*3 + 1, v___x_1983_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*3 + 2, v___x_2002_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*3 + 3, v___x_1983_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*3 + 4, v___x_1983_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*3 + 5, v___x_1983_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*3 + 6, v___x_1983_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*3 + 7, v___x_1983_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*3 + 8, v___x_2002_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*3 + 9, v___x_2002_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*3 + 10, v___x_2004_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*3 + 11, v___x_2002_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*3 + 12, v___x_2002_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*3 + 13, v___x_2006_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*3 + 14, v___x_1983_);
lean_inc(v___x_1981_);
v___x_2008_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_1981_, v___x_2007_, v___x_1983_, v___y_1989_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2010_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2009_);
lean_dec_ref_known(v___x_2008_, 1);
lean_inc(v_typesStx_1988_);
v___x_2010_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_1988_, v_a_2009_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2012_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2010_, 1);
v___x_2012_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(v_a_2009_, v_a_2011_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2014_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref_known(v___x_2012_, 1);
v___x_2014_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1990_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2014_, 1);
v___x_2016_ = lean_unsigned_to_nat(1024u);
v___x_2017_ = lean_unsigned_to_nat(9u);
v___x_2018_ = lean_unsigned_to_nat(5u);
v___x_2019_ = lean_unsigned_to_nat(8u);
v___x_2020_ = lean_unsigned_to_nat(10000u);
v___x_2021_ = lean_unsigned_to_nat(16u);
v___x_2022_ = lean_unsigned_to_nat(1048576u);
v___x_2023_ = lean_unsigned_to_nat(50u);
v___x_2024_ = lean_box(0);
v___x_2025_ = lean_alloc_ctor(0, 18, 35);
lean_ctor_set(v___x_2025_, 0, v___x_2016_);
lean_ctor_set(v___x_2025_, 1, v___x_2017_);
lean_ctor_set(v___x_2025_, 2, v___x_2018_);
lean_ctor_set(v___x_2025_, 3, v___x_2019_);
lean_ctor_set(v___x_2025_, 4, v___x_2019_);
lean_ctor_set(v___x_2025_, 5, v___x_2005_);
lean_ctor_set(v___x_2025_, 6, v___x_2005_);
lean_ctor_set(v___x_2025_, 7, v___x_1985_);
lean_ctor_set(v___x_2025_, 8, v___x_2003_);
lean_ctor_set(v___x_2025_, 9, v___x_2016_);
lean_ctor_set(v___x_2025_, 10, v___x_2020_);
lean_ctor_set(v___x_2025_, 11, v___x_2019_);
lean_ctor_set(v___x_2025_, 12, v___x_2021_);
lean_ctor_set(v___x_2025_, 13, v___x_2005_);
lean_ctor_set(v___x_2025_, 14, v___x_2022_);
lean_ctor_set(v___x_2025_, 15, v___x_2001_);
lean_ctor_set(v___x_2025_, 16, v___x_2023_);
lean_ctor_set(v___x_2025_, 17, v___x_2024_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18, v___x_2002_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 1, v___x_2002_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 2, v___x_2002_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 3, v___x_2002_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 4, v___x_2002_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 5, v___x_1983_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 6, v___x_1983_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 7, v___x_1983_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 8, v___x_2002_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 9, v___x_2002_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 10, v___x_2002_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 11, v___x_1983_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 12, v___x_2002_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 13, v___x_1983_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 14, v___x_1983_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 15, v___x_1983_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 16, v___x_2002_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 17, v___x_1983_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 18, v___x_2002_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 19, v___x_1983_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 20, v___x_1983_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 21, v___x_1983_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 22, v___x_2002_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 23, v___x_1983_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 24, v___x_1983_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 25, v___x_1983_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 26, v___x_1983_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 27, v___x_1983_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 28, v___x_1983_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 29, v___x_1983_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 30, v___x_1983_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 31, v___x_1983_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 32, v___x_2002_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 33, v___x_1983_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*18 + 34, v___x_1983_);
v___x_2026_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_2025_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v___x_2029_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2026_, 1);
lean_inc(v_a_2015_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set_tag(v___x_1999_, 1);
lean_ctor_set(v___x_1999_, 0, v_a_2015_);
v___x_2029_ = v___x_1999_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2015_);
v___x_2029_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_2030_; lean_object* v___f_2031_; lean_object* v___x_2032_; 
v___x_2030_ = lean_box(v___x_2002_);
v___f_2031_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___boxed), 21, 11);
lean_closure_set(v___f_2031_, 0, v___x_2029_);
lean_closure_set(v___f_2031_, 1, v_a_2013_);
lean_closure_set(v___f_2031_, 2, v_a_2015_);
lean_closure_set(v___f_2031_, 3, v___x_2030_);
lean_closure_set(v___f_2031_, 4, v___x_1974_);
lean_closure_set(v___f_2031_, 5, v___x_1975_);
lean_closure_set(v___f_2031_, 6, v___x_1976_);
lean_closure_set(v___f_2031_, 7, v___x_1981_);
lean_closure_set(v___f_2031_, 8, v_tk_1986_);
lean_closure_set(v___f_2031_, 9, v_typesStx_1988_);
lean_closure_set(v___f_2031_, 10, v___x_1985_);
v___x_2032_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___f_2031_, v_a_2027_, v___x_2024_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
return v___x_2032_;
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec(v_a_2015_);
lean_dec(v_a_2013_);
lean_del_object(v___x_1999_);
lean_dec(v_typesStx_1988_);
lean_dec(v_tk_1986_);
lean_dec(v___x_1981_);
v_a_2034_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2026_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2026_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec(v_a_2013_);
lean_del_object(v___x_1999_);
lean_dec(v_typesStx_1988_);
lean_dec(v_tk_1986_);
lean_dec(v___x_1981_);
v_a_2042_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2014_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2014_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_del_object(v___x_1999_);
lean_dec(v_typesStx_1988_);
lean_dec(v_tk_1986_);
lean_dec(v___x_1981_);
v_a_2050_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2012_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2012_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec(v_a_2009_);
lean_del_object(v___x_1999_);
lean_dec(v_typesStx_1988_);
lean_dec(v_tk_1986_);
lean_dec(v___x_1981_);
v_a_2058_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2010_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2010_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_del_object(v___x_1999_);
lean_dec(v_typesStx_1988_);
lean_dec(v_tk_1986_);
lean_dec(v___x_1981_);
v_a_2066_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2008_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2008_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
else
{
lean_dec(v_typesStx_1988_);
lean_dec(v_tk_1986_);
lean_dec(v___x_1981_);
return v___x_1997_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___boxed(lean_object* v_x_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic(v_x_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
lean_dec(v_a_2095_);
lean_dec_ref(v_a_2094_);
lean_dec(v_a_2093_);
lean_dec_ref(v_a_2092_);
lean_dec(v_a_2091_);
lean_dec_ref(v_a_2090_);
lean_dec(v_a_2089_);
lean_dec_ref(v_a_2088_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1(){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2106_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2107_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__1));
v___x_2108_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___closed__1));
v___x_2109_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___boxed), 10, 0);
v___x_2110_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2106_, v___x_2107_, v___x_2108_, v___x_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___boxed(lean_object* v_a_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1();
return v_res_2112_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_2119_, lean_object* v_x_2120_){
_start:
{
if (lean_obj_tag(v_x_2120_) == 1)
{
lean_object* v_pre_2121_; 
v_pre_2121_ = lean_ctor_get(v_x_2120_, 0);
switch(lean_obj_tag(v_pre_2121_))
{
case 1:
{
lean_object* v_pre_2122_; 
v_pre_2122_ = lean_ctor_get(v_pre_2121_, 0);
switch(lean_obj_tag(v_pre_2122_))
{
case 0:
{
lean_object* v_str_2123_; lean_object* v_str_2124_; lean_object* v___x_2125_; uint8_t v___x_2126_; 
v_str_2123_ = lean_ctor_get(v_x_2120_, 1);
v_str_2124_ = lean_ctor_get(v_pre_2121_, 1);
v___x_2125_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__0));
v___x_2126_ = lean_string_dec_eq(v_str_2124_, v___x_2125_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; uint8_t v___x_2128_; 
v___x_2127_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1));
v___x_2128_ = lean_string_dec_eq(v_str_2124_, v___x_2127_);
if (v___x_2128_ == 0)
{
return v___x_2128_;
}
else
{
lean_object* v___x_2129_; uint8_t v___x_2130_; 
v___x_2129_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_2130_ = lean_string_dec_eq(v_str_2123_, v___x_2129_);
if (v___x_2130_ == 0)
{
return v___x_2130_;
}
else
{
return v_suppressElabErrors_2119_;
}
}
}
else
{
lean_object* v___x_2131_; uint8_t v___x_2132_; 
v___x_2131_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_2132_ = lean_string_dec_eq(v_str_2123_, v___x_2131_);
if (v___x_2132_ == 0)
{
return v___x_2132_;
}
else
{
return v_suppressElabErrors_2119_;
}
}
}
case 1:
{
lean_object* v_pre_2133_; 
v_pre_2133_ = lean_ctor_get(v_pre_2122_, 0);
if (lean_obj_tag(v_pre_2133_) == 0)
{
lean_object* v_str_2134_; lean_object* v_str_2135_; lean_object* v_str_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; 
v_str_2134_ = lean_ctor_get(v_x_2120_, 1);
v_str_2135_ = lean_ctor_get(v_pre_2121_, 1);
v_str_2136_ = lean_ctor_get(v_pre_2122_, 1);
v___x_2137_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_2138_ = lean_string_dec_eq(v_str_2136_, v___x_2137_);
if (v___x_2138_ == 0)
{
return v___x_2138_;
}
else
{
lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2139_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_2140_ = lean_string_dec_eq(v_str_2135_, v___x_2139_);
if (v___x_2140_ == 0)
{
return v___x_2140_;
}
else
{
lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2141_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_2142_ = lean_string_dec_eq(v_str_2134_, v___x_2141_);
if (v___x_2142_ == 0)
{
return v___x_2142_;
}
else
{
return v_suppressElabErrors_2119_;
}
}
}
}
else
{
uint8_t v___x_2143_; 
v___x_2143_ = 0;
return v___x_2143_;
}
}
default: 
{
uint8_t v___x_2144_; 
v___x_2144_ = 0;
return v___x_2144_;
}
}
}
case 0:
{
lean_object* v_str_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; 
v_str_2145_ = lean_ctor_get(v_x_2120_, 1);
v___x_2146_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_2147_ = lean_string_dec_eq(v_str_2145_, v___x_2146_);
if (v___x_2147_ == 0)
{
return v___x_2147_;
}
else
{
return v_suppressElabErrors_2119_;
}
}
default: 
{
uint8_t v___x_2148_; 
v___x_2148_ = 0;
return v___x_2148_;
}
}
}
else
{
uint8_t v___x_2149_; 
v___x_2149_ = 0;
return v___x_2149_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_2150_, lean_object* v_x_2151_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2152_; uint8_t v_res_2153_; lean_object* v_r_2154_; 
v_suppressElabErrors_boxed_2152_ = lean_unbox(v_suppressElabErrors_2150_);
v_res_2153_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_2152_, v_x_2151_);
lean_dec(v_x_2151_);
v_r_2154_ = lean_box(v_res_2153_);
return v_r_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(lean_object* v_ref_2155_, lean_object* v_msgData_2156_, uint8_t v_severity_2157_, uint8_t v_isSilent_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
uint8_t v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v___y_2169_; uint8_t v___y_2170_; lean_object* v___y_2171_; lean_object* v_toCold_2172_; lean_object* v___y_2173_; lean_object* v___y_2202_; lean_object* v___y_2203_; uint8_t v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2206_; uint8_t v___y_2207_; uint8_t v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2229_; uint8_t v___y_2230_; lean_object* v___y_2231_; uint8_t v___y_2232_; lean_object* v___y_2233_; uint8_t v___y_2234_; lean_object* v___y_2235_; uint8_t v___y_2239_; uint8_t v___y_2240_; uint8_t v___x_2250_; uint8_t v___y_2252_; uint8_t v___x_2258_; 
v___x_2250_ = 2;
v___x_2258_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2157_, v___x_2250_);
if (v___x_2258_ == 0)
{
v___y_2252_ = v___x_2258_;
goto v___jp_2251_;
}
else
{
uint8_t v___x_2259_; 
lean_inc_ref(v_msgData_2156_);
v___x_2259_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2156_);
if (v___x_2259_ == 0)
{
v___y_2252_ = v___x_2259_;
goto v___jp_2251_;
}
else
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
lean_dec_ref(v_msgData_2156_);
v___x_2260_ = lean_box(0);
v___x_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
return v___x_2261_;
}
}
v___jp_2164_:
{
lean_object* v_currNamespace_2174_; lean_object* v_openDecls_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v_env_2180_; lean_object* v_nextMacroScope_2181_; lean_object* v_ngen_2182_; lean_object* v_auxDeclNGen_2183_; lean_object* v_traceState_2184_; lean_object* v_cache_2185_; lean_object* v_recordedDeps_2186_; lean_object* v_messages_2187_; lean_object* v_infoState_2188_; lean_object* v_snapshotTasks_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2200_; 
v_currNamespace_2174_ = lean_ctor_get(v_toCold_2172_, 4);
v_openDecls_2175_ = lean_ctor_get(v_toCold_2172_, 5);
lean_inc(v_openDecls_2175_);
lean_inc(v_currNamespace_2174_);
v___x_2176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2176_, 0, v_currNamespace_2174_);
lean_ctor_set(v___x_2176_, 1, v_openDecls_2175_);
v___x_2177_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
lean_ctor_set(v___x_2177_, 1, v___y_2169_);
lean_inc_ref(v___y_2167_);
lean_inc_ref(v___y_2171_);
v___x_2178_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2178_, 0, v___y_2171_);
lean_ctor_set(v___x_2178_, 1, v___y_2168_);
lean_ctor_set(v___x_2178_, 2, v___y_2166_);
lean_ctor_set(v___x_2178_, 3, v___y_2167_);
lean_ctor_set(v___x_2178_, 4, v___x_2177_);
lean_ctor_set_uint8(v___x_2178_, sizeof(void*)*5, v___y_2170_);
lean_ctor_set_uint8(v___x_2178_, sizeof(void*)*5 + 1, v___y_2165_);
lean_ctor_set_uint8(v___x_2178_, sizeof(void*)*5 + 2, v_isSilent_2158_);
v___x_2179_ = lean_st_ref_take(v___y_2173_);
v_env_2180_ = lean_ctor_get(v___x_2179_, 0);
v_nextMacroScope_2181_ = lean_ctor_get(v___x_2179_, 1);
v_ngen_2182_ = lean_ctor_get(v___x_2179_, 2);
v_auxDeclNGen_2183_ = lean_ctor_get(v___x_2179_, 3);
v_traceState_2184_ = lean_ctor_get(v___x_2179_, 4);
v_cache_2185_ = lean_ctor_get(v___x_2179_, 5);
v_recordedDeps_2186_ = lean_ctor_get(v___x_2179_, 6);
v_messages_2187_ = lean_ctor_get(v___x_2179_, 7);
v_infoState_2188_ = lean_ctor_get(v___x_2179_, 8);
v_snapshotTasks_2189_ = lean_ctor_get(v___x_2179_, 9);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2191_ = v___x_2179_;
v_isShared_2192_ = v_isSharedCheck_2200_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_snapshotTasks_2189_);
lean_inc(v_infoState_2188_);
lean_inc(v_messages_2187_);
lean_inc(v_recordedDeps_2186_);
lean_inc(v_cache_2185_);
lean_inc(v_traceState_2184_);
lean_inc(v_auxDeclNGen_2183_);
lean_inc(v_ngen_2182_);
lean_inc(v_nextMacroScope_2181_);
lean_inc(v_env_2180_);
lean_dec(v___x_2179_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2200_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2193_ = lean_box(0);
v___x_2194_ = l_Lean_MessageLog_add(v___x_2178_, v_messages_2187_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 7, v___x_2194_);
v___x_2196_ = v___x_2191_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_env_2180_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_nextMacroScope_2181_);
lean_ctor_set(v_reuseFailAlloc_2199_, 2, v_ngen_2182_);
lean_ctor_set(v_reuseFailAlloc_2199_, 3, v_auxDeclNGen_2183_);
lean_ctor_set(v_reuseFailAlloc_2199_, 4, v_traceState_2184_);
lean_ctor_set(v_reuseFailAlloc_2199_, 5, v_cache_2185_);
lean_ctor_set(v_reuseFailAlloc_2199_, 6, v_recordedDeps_2186_);
lean_ctor_set(v_reuseFailAlloc_2199_, 7, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2199_, 8, v_infoState_2188_);
lean_ctor_set(v_reuseFailAlloc_2199_, 9, v_snapshotTasks_2189_);
v___x_2196_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = lean_st_ref_put(v___y_2173_, v___x_2196_);
v___x_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2193_);
return v___x_2198_;
}
}
}
v___jp_2201_:
{
lean_object* v_fileName_2210_; lean_object* v_fileMap_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2227_; 
v_fileName_2210_ = lean_ctor_get(v___y_2206_, 0);
v_fileMap_2211_ = lean_ctor_get(v___y_2206_, 1);
v___x_2212_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2156_);
v___x_2213_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v___x_2212_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2216_ = v___x_2213_;
v_isShared_2217_ = v_isSharedCheck_2227_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2213_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2227_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
lean_inc_ref_n(v_fileMap_2211_, 2);
v___x_2218_ = l_Lean_FileMap_toPosition(v_fileMap_2211_, v___y_2205_);
lean_dec(v___y_2205_);
v___x_2219_ = l_Lean_FileMap_toPosition(v_fileMap_2211_, v___y_2209_);
lean_dec(v___y_2209_);
v___x_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
v___x_2221_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5));
if (v___y_2207_ == 0)
{
lean_del_object(v___x_2216_);
lean_dec_ref(v___y_2203_);
v___y_2165_ = v___y_2204_;
v___y_2166_ = v___x_2220_;
v___y_2167_ = v___x_2221_;
v___y_2168_ = v___x_2218_;
v___y_2169_ = v_a_2214_;
v___y_2170_ = v___y_2208_;
v___y_2171_ = v_fileName_2210_;
v_toCold_2172_ = v___y_2202_;
v___y_2173_ = v___y_2162_;
goto v___jp_2164_;
}
else
{
uint8_t v___x_2222_; 
lean_inc(v_a_2214_);
v___x_2222_ = l_Lean_MessageData_hasTag(v___y_2203_, v_a_2214_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; lean_object* v___x_2225_; 
lean_dec_ref_known(v___x_2220_, 1);
lean_dec_ref(v___x_2218_);
lean_dec(v_a_2214_);
v___x_2223_ = lean_box(0);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 0, v___x_2223_);
v___x_2225_ = v___x_2216_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
else
{
lean_del_object(v___x_2216_);
v___y_2165_ = v___y_2204_;
v___y_2166_ = v___x_2220_;
v___y_2167_ = v___x_2221_;
v___y_2168_ = v___x_2218_;
v___y_2169_ = v_a_2214_;
v___y_2170_ = v___y_2208_;
v___y_2171_ = v_fileName_2210_;
v_toCold_2172_ = v___y_2202_;
v___y_2173_ = v___y_2162_;
goto v___jp_2164_;
}
}
}
}
v___jp_2228_:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_Syntax_getTailPos_x3f(v___y_2233_, v___y_2234_);
lean_dec(v___y_2233_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_inc(v___y_2235_);
v___y_2202_ = v___y_2229_;
v___y_2203_ = v___y_2231_;
v___y_2204_ = v___y_2232_;
v___y_2205_ = v___y_2235_;
v___y_2206_ = v___y_2229_;
v___y_2207_ = v___y_2230_;
v___y_2208_ = v___y_2234_;
v___y_2209_ = v___y_2235_;
goto v___jp_2201_;
}
else
{
lean_object* v_val_2237_; 
v_val_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_val_2237_);
lean_dec_ref_known(v___x_2236_, 1);
v___y_2202_ = v___y_2229_;
v___y_2203_ = v___y_2231_;
v___y_2204_ = v___y_2232_;
v___y_2205_ = v___y_2235_;
v___y_2206_ = v___y_2229_;
v___y_2207_ = v___y_2230_;
v___y_2208_ = v___y_2234_;
v___y_2209_ = v_val_2237_;
goto v___jp_2201_;
}
}
v___jp_2238_:
{
lean_object* v_toCold_2241_; lean_object* v_ref_2242_; uint8_t v_suppressElabErrors_2243_; lean_object* v___x_2244_; lean_object* v___f_2245_; lean_object* v_ref_2246_; lean_object* v___x_2247_; 
v_toCold_2241_ = lean_ctor_get(v___y_2161_, 0);
v_ref_2242_ = lean_ctor_get(v___y_2161_, 2);
v_suppressElabErrors_2243_ = lean_ctor_get_uint8(v___y_2161_, sizeof(void*)*3 + 2);
v___x_2244_ = lean_box(v_suppressElabErrors_2243_);
v___f_2245_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2245_, 0, v___x_2244_);
v_ref_2246_ = l_Lean_replaceRef(v_ref_2155_, v_ref_2242_);
v___x_2247_ = l_Lean_Syntax_getPos_x3f(v_ref_2246_, v___y_2239_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v___x_2248_; 
v___x_2248_ = lean_unsigned_to_nat(0u);
v___y_2229_ = v_toCold_2241_;
v___y_2230_ = v_suppressElabErrors_2243_;
v___y_2231_ = v___f_2245_;
v___y_2232_ = v___y_2240_;
v___y_2233_ = v_ref_2246_;
v___y_2234_ = v___y_2239_;
v___y_2235_ = v___x_2248_;
goto v___jp_2228_;
}
else
{
lean_object* v_val_2249_; 
v_val_2249_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_val_2249_);
lean_dec_ref_known(v___x_2247_, 1);
v___y_2229_ = v_toCold_2241_;
v___y_2230_ = v_suppressElabErrors_2243_;
v___y_2231_ = v___f_2245_;
v___y_2232_ = v___y_2240_;
v___y_2233_ = v_ref_2246_;
v___y_2234_ = v___y_2239_;
v___y_2235_ = v_val_2249_;
goto v___jp_2228_;
}
}
v___jp_2251_:
{
uint8_t v___x_2253_; uint8_t v___x_2254_; 
v___x_2253_ = 1;
v___x_2254_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2157_, v___x_2253_);
if (v___x_2254_ == 0)
{
v___y_2239_ = v___y_2252_;
v___y_2240_ = v_severity_2157_;
goto v___jp_2238_;
}
else
{
lean_object* v___x_2255_; lean_object* v___x_2256_; uint8_t v___x_2257_; 
v___x_2255_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2161_);
v___x_2256_ = l_Lean_warningAsError;
v___x_2257_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v___x_2255_, v___x_2256_);
lean_dec_ref(v___x_2255_);
if (v___x_2257_ == 0)
{
v___y_2239_ = v___y_2252_;
v___y_2240_ = v_severity_2157_;
goto v___jp_2238_;
}
else
{
v___y_2239_ = v___y_2252_;
v___y_2240_ = v___x_2250_;
goto v___jp_2238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_2262_, lean_object* v_msgData_2263_, lean_object* v_severity_2264_, lean_object* v_isSilent_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
uint8_t v_severity_boxed_2271_; uint8_t v_isSilent_boxed_2272_; lean_object* v_res_2273_; 
v_severity_boxed_2271_ = lean_unbox(v_severity_2264_);
v_isSilent_boxed_2272_ = lean_unbox(v_isSilent_2265_);
v_res_2273_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(v_ref_2262_, v_msgData_2263_, v_severity_boxed_2271_, v_isSilent_boxed_2272_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v_ref_2262_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(lean_object* v_msgData_2274_, uint8_t v_severity_2275_, uint8_t v_isSilent_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v_ref_2282_; lean_object* v___x_2283_; 
v_ref_2282_ = lean_ctor_get(v___y_2279_, 2);
v___x_2283_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(v_ref_2282_, v_msgData_2274_, v_severity_2275_, v_isSilent_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0___boxed(lean_object* v_msgData_2284_, lean_object* v_severity_2285_, lean_object* v_isSilent_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
uint8_t v_severity_boxed_2292_; uint8_t v_isSilent_boxed_2293_; lean_object* v_res_2294_; 
v_severity_boxed_2292_ = lean_unbox(v_severity_2285_);
v_isSilent_boxed_2293_ = lean_unbox(v_isSilent_2286_);
v_res_2294_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(v_msgData_2284_, v_severity_boxed_2292_, v_isSilent_boxed_2293_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(lean_object* v_msgData_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
uint8_t v___x_2301_; uint8_t v___x_2302_; lean_object* v___x_2303_; 
v___x_2301_ = 1;
v___x_2302_ = 0;
v___x_2303_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(v_msgData_2295_, v___x_2301_, v___x_2302_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0___boxed(lean_object* v_msgData_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(v_msgData_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
return v_res_2310_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__2));
v___x_2316_ = l_Lean_stringToMessageData(v___x_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0(lean_object* v___x_2317_, lean_object* v___x_2318_, lean_object* v___x_2319_, lean_object* v___x_2320_, lean_object* v_tk_2321_, lean_object* v_typesStx_2322_, lean_object* v___x_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v_ref_2329_; uint8_t v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___y_2340_; 
v_ref_2329_ = lean_ctor_get(v___y_2326_, 2);
v___x_2330_ = 0;
v___x_2331_ = l_Lean_SourceInfo_fromRef(v_ref_2329_, v___x_2330_);
v___x_2332_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1));
v___x_2333_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__0));
v___x_2334_ = l_Lean_Name_mkStr4(v___x_2317_, v___x_2318_, v___x_2319_, v___x_2333_);
v___x_2335_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__1));
lean_inc(v___x_2331_);
v___x_2336_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2331_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3));
v___x_2338_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4);
if (lean_obj_tag(v_typesStx_2322_) == 1)
{
lean_object* v_val_2361_; lean_object* v___x_2362_; 
v_val_2361_ = lean_ctor_get(v_typesStx_2322_, 0);
lean_inc(v_val_2361_);
lean_dec_ref_known(v_typesStx_2322_, 1);
v___x_2362_ = l_Array_mkArray1___redArg(v_val_2361_);
v___y_2340_ = v___x_2362_;
goto v___jp_2339_;
}
else
{
lean_object* v___x_2363_; 
lean_dec(v_typesStx_2322_);
v___x_2363_ = lean_mk_empty_array_with_capacity(v___x_2323_);
v___y_2340_ = v___x_2363_;
goto v___jp_2339_;
}
v___jp_2339_:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2341_ = l_Array_append___redArg(v___x_2338_, v___y_2340_);
lean_dec_ref(v___y_2340_);
lean_inc(v___x_2331_);
v___x_2342_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2331_);
lean_ctor_set(v___x_2342_, 1, v___x_2337_);
lean_ctor_set(v___x_2342_, 2, v___x_2341_);
v___x_2343_ = l_Lean_Syntax_node3(v___x_2331_, v___x_2334_, v___x_2336_, v___x_2320_, v___x_2342_);
v___x_2344_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__3, &l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__3);
v___x_2345_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(v___x_2344_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2359_; 
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2359_ == 0)
{
lean_object* v_unused_2360_; 
v_unused_2360_ = lean_ctor_get(v___x_2345_, 0);
lean_dec(v_unused_2360_);
v___x_2347_ = v___x_2345_;
v_isShared_2348_ = v_isSharedCheck_2359_;
goto v_resetjp_2346_;
}
else
{
lean_dec(v___x_2345_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2359_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2353_; 
v___x_2349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2332_);
lean_ctor_set(v___x_2349_, 1, v___x_2343_);
v___x_2350_ = lean_box(0);
v___x_2351_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2349_);
lean_ctor_set(v___x_2351_, 1, v___x_2350_);
lean_ctor_set(v___x_2351_, 2, v___x_2350_);
lean_ctor_set(v___x_2351_, 3, v___x_2350_);
lean_ctor_set(v___x_2351_, 4, v___x_2350_);
lean_ctor_set(v___x_2351_, 5, v___x_2350_);
lean_inc(v_ref_2329_);
if (v_isShared_2348_ == 0)
{
lean_ctor_set_tag(v___x_2347_, 1);
lean_ctor_set(v___x_2347_, 0, v_ref_2329_);
v___x_2353_ = v___x_2347_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_ref_2329_);
v___x_2353_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
lean_object* v___x_2354_; uint8_t v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2354_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__2));
v___x_2355_ = 4;
v___x_2356_ = l_Lean_MessageData_nil;
v___x_2357_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2321_, v___x_2351_, v___x_2353_, v___x_2354_, v___x_2350_, v___x_2355_, v___x_2356_, v___y_2326_, v___y_2327_);
return v___x_2357_;
}
}
}
else
{
lean_dec(v___x_2343_);
lean_dec(v_tk_2321_);
return v___x_2345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___boxed(lean_object* v___x_2364_, lean_object* v___x_2365_, lean_object* v___x_2366_, lean_object* v___x_2367_, lean_object* v_tk_2368_, lean_object* v_typesStx_2369_, lean_object* v___x_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0(v___x_2364_, v___x_2365_, v___x_2366_, v___x_2367_, v_tk_2368_, v_typesStx_2369_, v___x_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___x_2370_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic(lean_object* v_x_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; uint8_t v___x_2399_; 
v___x_2395_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0));
v___x_2396_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1));
v___x_2397_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1));
v___x_2398_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0));
lean_inc(v_x_2385_);
v___x_2399_ = l_Lean_Syntax_isOfKind(v_x_2385_, v___x_2398_);
if (v___x_2399_ == 0)
{
lean_object* v___x_2400_; 
lean_dec(v_x_2385_);
v___x_2400_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2400_;
}
else
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; uint8_t v___x_2404_; 
v___x_2401_ = lean_unsigned_to_nat(1u);
v___x_2402_ = l_Lean_Syntax_getArg(v_x_2385_, v___x_2401_);
v___x_2403_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_2402_);
v___x_2404_ = l_Lean_Syntax_isOfKind(v___x_2402_, v___x_2403_);
if (v___x_2404_ == 0)
{
lean_object* v___x_2405_; 
lean_dec(v___x_2402_);
lean_dec(v_x_2385_);
v___x_2405_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2405_;
}
else
{
lean_object* v___x_2406_; lean_object* v_tk_2407_; lean_object* v_typesStx_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___x_2503_; lean_object* v___x_2504_; uint8_t v___x_2505_; 
v___x_2406_ = lean_unsigned_to_nat(0u);
v_tk_2407_ = l_Lean_Syntax_getArg(v_x_2385_, v___x_2406_);
v___x_2503_ = lean_unsigned_to_nat(2u);
v___x_2504_ = l_Lean_Syntax_getArg(v_x_2385_, v___x_2503_);
v___x_2505_ = l_Lean_Syntax_isNone(v___x_2504_);
if (v___x_2505_ == 0)
{
uint8_t v___x_2506_; 
lean_inc(v___x_2504_);
v___x_2506_ = l_Lean_Syntax_matchesNull(v___x_2504_, v___x_2401_);
if (v___x_2506_ == 0)
{
lean_object* v___x_2507_; 
lean_dec(v___x_2504_);
lean_dec(v_tk_2407_);
lean_dec(v___x_2402_);
lean_dec(v_x_2385_);
v___x_2507_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2507_;
}
else
{
lean_object* v_typesStx_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; 
v_typesStx_2508_ = l_Lean_Syntax_getArg(v___x_2504_, v___x_2406_);
lean_dec(v___x_2504_);
v___x_2509_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_typesStx_2508_);
v___x_2510_ = l_Lean_Syntax_isOfKind(v_typesStx_2508_, v___x_2509_);
if (v___x_2510_ == 0)
{
lean_object* v___x_2511_; 
lean_dec(v_typesStx_2508_);
lean_dec(v_tk_2407_);
lean_dec(v___x_2402_);
lean_dec(v_x_2385_);
v___x_2511_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2511_;
}
else
{
lean_object* v___x_2512_; 
v___x_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2512_, 0, v_typesStx_2508_);
v_typesStx_2409_ = v___x_2512_;
v___y_2410_ = v_a_2386_;
v___y_2411_ = v_a_2387_;
v___y_2412_ = v_a_2388_;
v___y_2413_ = v_a_2389_;
v___y_2414_ = v_a_2390_;
v___y_2415_ = v_a_2391_;
v___y_2416_ = v_a_2392_;
v___y_2417_ = v_a_2393_;
goto v___jp_2408_;
}
}
}
else
{
lean_object* v___x_2513_; 
lean_dec(v___x_2504_);
v___x_2513_ = lean_box(0);
v_typesStx_2409_ = v___x_2513_;
v___y_2410_ = v_a_2386_;
v___y_2411_ = v_a_2387_;
v___y_2412_ = v_a_2388_;
v___y_2413_ = v_a_2389_;
v___y_2414_ = v_a_2390_;
v___y_2415_ = v_a_2391_;
v___y_2416_ = v_a_2392_;
v___y_2417_ = v_a_2393_;
goto v___jp_2408_;
}
v___jp_2408_:
{
lean_object* v___x_2418_; lean_object* v_path_2419_; lean_object* v___x_2420_; uint8_t v___x_2421_; 
v___x_2418_ = lean_unsigned_to_nat(3u);
v_path_2419_ = l_Lean_Syntax_getArg(v_x_2385_, v___x_2418_);
lean_dec(v_x_2385_);
v___x_2420_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__2));
lean_inc(v_path_2419_);
v___x_2421_ = l_Lean_Syntax_isOfKind(v_path_2419_, v___x_2420_);
if (v___x_2421_ == 0)
{
lean_object* v___x_2422_; 
lean_dec(v_path_2419_);
lean_dec(v_typesStx_2409_);
lean_dec(v_tk_2407_);
lean_dec(v___x_2402_);
v___x_2422_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2422_;
}
else
{
lean_object* v___f_2423_; lean_object* v___x_2424_; 
lean_inc(v_typesStx_2409_);
lean_inc(v___x_2402_);
v___f_2423_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___boxed), 12, 7);
lean_closure_set(v___f_2423_, 0, v___x_2395_);
lean_closure_set(v___f_2423_, 1, v___x_2396_);
lean_closure_set(v___f_2423_, 2, v___x_2397_);
lean_closure_set(v___f_2423_, 3, v___x_2402_);
lean_closure_set(v___f_2423_, 4, v_tk_2407_);
lean_closure_set(v___f_2423_, 5, v_typesStx_2409_);
lean_closure_set(v___f_2423_, 6, v___x_2406_);
v___x_2424_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_2416_, v___y_2417_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2501_; 
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2501_ == 0)
{
lean_object* v_unused_2502_; 
v_unused_2502_ = lean_ctor_get(v___x_2424_, 0);
lean_dec(v_unused_2502_);
v___x_2426_ = v___x_2424_;
v_isShared_2427_ = v_isSharedCheck_2501_;
goto v_resetjp_2425_;
}
else
{
lean_dec(v___x_2424_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2501_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2428_; uint8_t v___x_2429_; lean_object* v___x_2430_; uint8_t v___x_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2428_ = lean_unsigned_to_nat(10u);
v___x_2429_ = 0;
v___x_2430_ = lean_unsigned_to_nat(100000u);
v___x_2431_ = 0;
v___x_2432_ = lean_unsigned_to_nat(1000u);
v___x_2433_ = 1;
v___x_2434_ = lean_alloc_ctor(0, 3, 15);
lean_ctor_set(v___x_2434_, 0, v___x_2428_);
lean_ctor_set(v___x_2434_, 1, v___x_2430_);
lean_ctor_set(v___x_2434_, 2, v___x_2432_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*3, v___x_2404_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*3 + 1, v___x_2404_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*3 + 2, v___x_2429_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*3 + 3, v___x_2404_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*3 + 4, v___x_2404_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*3 + 5, v___x_2404_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*3 + 6, v___x_2404_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*3 + 7, v___x_2404_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*3 + 8, v___x_2429_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*3 + 9, v___x_2429_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*3 + 10, v___x_2431_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*3 + 11, v___x_2429_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*3 + 12, v___x_2429_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*3 + 13, v___x_2433_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*3 + 14, v___x_2404_);
v___x_2435_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_2402_, v___x_2434_, v___x_2404_, v___y_2410_, v___y_2416_, v___y_2417_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2437_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2435_, 1);
v___x_2437_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_2409_, v_a_2436_, v___y_2416_, v___y_2417_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2437_, 1);
v___x_2439_ = l_Lean_TSyntax_getString(v_path_2419_);
lean_dec(v_path_2419_);
v___x_2440_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v___x_2439_, v_a_2436_, v_a_2438_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; lean_object* v___x_2442_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_a_2441_);
lean_dec_ref_known(v___x_2440_, 1);
v___x_2442_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2411_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_a_2443_);
lean_dec_ref_known(v___x_2442_, 1);
v___x_2444_ = lean_unsigned_to_nat(1024u);
v___x_2445_ = lean_unsigned_to_nat(9u);
v___x_2446_ = lean_unsigned_to_nat(5u);
v___x_2447_ = lean_unsigned_to_nat(8u);
v___x_2448_ = lean_unsigned_to_nat(10000u);
v___x_2449_ = lean_unsigned_to_nat(16u);
v___x_2450_ = lean_unsigned_to_nat(1048576u);
v___x_2451_ = lean_unsigned_to_nat(50u);
v___x_2452_ = lean_box(0);
v___x_2453_ = lean_alloc_ctor(0, 18, 35);
lean_ctor_set(v___x_2453_, 0, v___x_2444_);
lean_ctor_set(v___x_2453_, 1, v___x_2445_);
lean_ctor_set(v___x_2453_, 2, v___x_2446_);
lean_ctor_set(v___x_2453_, 3, v___x_2447_);
lean_ctor_set(v___x_2453_, 4, v___x_2447_);
lean_ctor_set(v___x_2453_, 5, v___x_2432_);
lean_ctor_set(v___x_2453_, 6, v___x_2432_);
lean_ctor_set(v___x_2453_, 7, v___x_2406_);
lean_ctor_set(v___x_2453_, 8, v___x_2430_);
lean_ctor_set(v___x_2453_, 9, v___x_2444_);
lean_ctor_set(v___x_2453_, 10, v___x_2448_);
lean_ctor_set(v___x_2453_, 11, v___x_2447_);
lean_ctor_set(v___x_2453_, 12, v___x_2449_);
lean_ctor_set(v___x_2453_, 13, v___x_2432_);
lean_ctor_set(v___x_2453_, 14, v___x_2450_);
lean_ctor_set(v___x_2453_, 15, v___x_2428_);
lean_ctor_set(v___x_2453_, 16, v___x_2451_);
lean_ctor_set(v___x_2453_, 17, v___x_2452_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18, v___x_2429_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 1, v___x_2429_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 2, v___x_2429_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 3, v___x_2429_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 4, v___x_2429_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 5, v___x_2404_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 6, v___x_2404_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 7, v___x_2404_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 8, v___x_2429_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 9, v___x_2429_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 10, v___x_2429_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 11, v___x_2404_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 12, v___x_2429_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 13, v___x_2404_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 14, v___x_2404_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 15, v___x_2404_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 16, v___x_2429_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 17, v___x_2404_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 18, v___x_2429_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 19, v___x_2404_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 20, v___x_2404_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 21, v___x_2404_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 22, v___x_2429_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 23, v___x_2404_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 24, v___x_2404_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 25, v___x_2404_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 26, v___x_2404_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 27, v___x_2404_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 28, v___x_2404_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 29, v___x_2404_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 30, v___x_2404_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 31, v___x_2404_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 32, v___x_2429_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 33, v___x_2404_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*18 + 34, v___x_2404_);
v___x_2454_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_2453_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2455_);
lean_dec_ref_known(v___x_2454_, 1);
if (v_isShared_2427_ == 0)
{
lean_ctor_set_tag(v___x_2426_, 1);
lean_ctor_set(v___x_2426_, 0, v_a_2443_);
v___x_2457_ = v___x_2426_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2443_);
v___x_2457_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed), 13, 3);
lean_closure_set(v___x_2458_, 0, v___x_2457_);
lean_closure_set(v___x_2458_, 1, v_a_2441_);
lean_closure_set(v___x_2458_, 2, v___f_2423_);
v___x_2459_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___x_2458_, v_a_2455_, v___x_2452_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
return v___x_2459_;
}
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec(v_a_2443_);
lean_dec(v_a_2441_);
lean_del_object(v___x_2426_);
lean_dec_ref(v___f_2423_);
v_a_2461_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2454_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2454_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec(v_a_2441_);
lean_del_object(v___x_2426_);
lean_dec_ref(v___f_2423_);
v_a_2469_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2442_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2442_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_del_object(v___x_2426_);
lean_dec_ref(v___f_2423_);
v_a_2477_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2440_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2440_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec(v_a_2436_);
lean_del_object(v___x_2426_);
lean_dec_ref(v___f_2423_);
lean_dec(v_path_2419_);
v_a_2485_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2437_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2437_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_del_object(v___x_2426_);
lean_dec_ref(v___f_2423_);
lean_dec(v_path_2419_);
lean_dec(v_typesStx_2409_);
v_a_2493_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2435_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2435_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
}
else
{
lean_dec_ref(v___f_2423_);
lean_dec(v_path_2419_);
lean_dec(v_typesStx_2409_);
lean_dec(v___x_2402_);
return v___x_2424_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___boxed(lean_object* v_x_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic(v_x_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_);
lean_dec(v_a_2522_);
lean_dec_ref(v_a_2521_);
lean_dec(v_a_2520_);
lean_dec_ref(v_a_2519_);
lean_dec(v_a_2518_);
lean_dec_ref(v_a_2517_);
lean_dec(v_a_2516_);
lean_dec_ref(v_a_2515_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1(){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2533_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2534_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0));
v___x_2535_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___closed__1));
v___x_2536_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___boxed), 10, 0);
v___x_2537_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2533_, v___x_2534_, v___x_2535_, v___x_2536_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___boxed(lean_object* v_a_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1();
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0(lean_object* v___x_2540_, lean_object* v___x_2541_, lean_object* v___x_2542_, uint8_t v___x_2543_, lean_object* v___x_2544_, lean_object* v___x_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2556_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1);
v___x_2557_ = lean_box(0);
v___x_2558_ = lean_mk_array(v___x_2540_, v___x_2557_);
lean_inc(v___x_2541_);
v___x_2559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2541_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
lean_inc_ref_n(v___x_2559_, 6);
v___x_2560_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
lean_ctor_set(v___x_2560_, 1, v___x_2559_);
lean_ctor_set(v___x_2560_, 2, v___x_2559_);
lean_ctor_set(v___x_2560_, 3, v___x_2559_);
v___x_2561_ = lean_mk_empty_array_with_capacity(v___x_2541_);
v___x_2562_ = lean_mk_empty_array_with_capacity(v___x_2541_);
lean_dec(v___x_2541_);
lean_inc_ref(v___x_2562_);
v___x_2563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2559_);
lean_ctor_set(v___x_2563_, 1, v___x_2559_);
lean_ctor_set(v___x_2563_, 2, v___x_2559_);
lean_ctor_set(v___x_2563_, 3, v___x_2562_);
lean_ctor_set(v___x_2563_, 4, v___x_2562_);
v___x_2564_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2564_, 0, v___x_2556_);
lean_ctor_set(v___x_2564_, 1, v___x_2560_);
lean_ctor_set(v___x_2564_, 2, v___x_2542_);
lean_ctor_set(v___x_2564_, 3, v___x_2561_);
lean_ctor_set(v___x_2564_, 4, v___x_2563_);
lean_ctor_set_uint8(v___x_2564_, sizeof(void*)*5, v___x_2543_);
v___x_2565_ = lean_st_mk_ref(v___x_2564_);
v___x_2566_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_2544_, v___x_2545_, v___x_2565_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2576_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2569_ = v___x_2566_;
v_isShared_2570_ = v_isSharedCheck_2576_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2566_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2576_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2574_; 
v___x_2571_ = lean_st_ref_get(v___x_2565_);
lean_dec(v___x_2565_);
v___x_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2572_, 0, v_a_2567_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2572_);
v___x_2574_ = v___x_2569_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2572_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
lean_dec(v___x_2565_);
v_a_2577_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2566_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2566_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0___boxed(lean_object* v___x_2585_, lean_object* v___x_2586_, lean_object* v___x_2587_, lean_object* v___x_2588_, lean_object* v___x_2589_, lean_object* v___x_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
uint8_t v___x_3518__boxed_2601_; lean_object* v_res_2602_; 
v___x_3518__boxed_2601_ = lean_unbox(v___x_2588_);
v_res_2602_ = l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0(v___x_2585_, v___x_2586_, v___x_2587_, v___x_3518__boxed_2601_, v___x_2589_, v___x_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___x_2590_);
lean_dec(v___x_2589_);
return v_res_2602_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_2603_, lean_object* v_i_2604_, lean_object* v_k_2605_){
_start:
{
lean_object* v___x_2606_; uint8_t v___x_2607_; 
v___x_2606_ = lean_array_get_size(v_keys_2603_);
v___x_2607_ = lean_nat_dec_lt(v_i_2604_, v___x_2606_);
if (v___x_2607_ == 0)
{
lean_dec(v_i_2604_);
return v___x_2607_;
}
else
{
lean_object* v_k_x27_2608_; uint8_t v___x_2609_; 
v_k_x27_2608_ = lean_array_fget_borrowed(v_keys_2603_, v_i_2604_);
v___x_2609_ = l_Lean_instBEqMVarId_beq(v_k_2605_, v_k_x27_2608_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = lean_unsigned_to_nat(1u);
v___x_2611_ = lean_nat_add(v_i_2604_, v___x_2610_);
lean_dec(v_i_2604_);
v_i_2604_ = v___x_2611_;
goto _start;
}
else
{
lean_dec(v_i_2604_);
return v___x_2607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_2613_, lean_object* v_i_2614_, lean_object* v_k_2615_){
_start:
{
uint8_t v_res_2616_; lean_object* v_r_2617_; 
v_res_2616_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2613_, v_i_2614_, v_k_2615_);
lean_dec(v_k_2615_);
lean_dec_ref(v_keys_2613_);
v_r_2617_ = lean_box(v_res_2616_);
return v_r_2617_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2618_, size_t v_x_2619_, lean_object* v_x_2620_){
_start:
{
if (lean_obj_tag(v_x_2618_) == 0)
{
lean_object* v_es_2621_; lean_object* v___x_2622_; size_t v___x_2623_; size_t v___x_2624_; lean_object* v_j_2625_; lean_object* v___x_2626_; 
v_es_2621_ = lean_ctor_get(v_x_2618_, 0);
v___x_2622_ = lean_box(2);
v___x_2623_ = ((size_t)31ULL);
v___x_2624_ = lean_usize_land(v_x_2619_, v___x_2623_);
v_j_2625_ = lean_usize_to_nat(v___x_2624_);
v___x_2626_ = lean_array_get_borrowed(v___x_2622_, v_es_2621_, v_j_2625_);
lean_dec(v_j_2625_);
switch(lean_obj_tag(v___x_2626_))
{
case 0:
{
lean_object* v_key_2627_; uint8_t v___x_2628_; 
v_key_2627_ = lean_ctor_get(v___x_2626_, 0);
v___x_2628_ = l_Lean_instBEqMVarId_beq(v_x_2620_, v_key_2627_);
return v___x_2628_;
}
case 1:
{
lean_object* v_node_2629_; size_t v___x_2630_; size_t v___x_2631_; 
v_node_2629_ = lean_ctor_get(v___x_2626_, 0);
v___x_2630_ = ((size_t)5ULL);
v___x_2631_ = lean_usize_shift_right(v_x_2619_, v___x_2630_);
v_x_2618_ = v_node_2629_;
v_x_2619_ = v___x_2631_;
goto _start;
}
default: 
{
uint8_t v___x_2633_; 
v___x_2633_ = 0;
return v___x_2633_;
}
}
}
else
{
lean_object* v_ks_2634_; lean_object* v___x_2635_; uint8_t v___x_2636_; 
v_ks_2634_ = lean_ctor_get(v_x_2618_, 0);
v___x_2635_ = lean_unsigned_to_nat(0u);
v___x_2636_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_2634_, v___x_2635_, v_x_2620_);
return v___x_2636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2637_, lean_object* v_x_2638_, lean_object* v_x_2639_){
_start:
{
size_t v_x_3636__boxed_2640_; uint8_t v_res_2641_; lean_object* v_r_2642_; 
v_x_3636__boxed_2640_ = lean_unbox_usize(v_x_2638_);
lean_dec(v_x_2638_);
v_res_2641_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_2637_, v_x_3636__boxed_2640_, v_x_2639_);
lean_dec(v_x_2639_);
lean_dec_ref(v_x_2637_);
v_r_2642_ = lean_box(v_res_2641_);
return v_r_2642_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(lean_object* v_x_2643_, lean_object* v_x_2644_){
_start:
{
uint64_t v___x_2645_; size_t v___x_2646_; uint8_t v___x_2647_; 
v___x_2645_ = l_Lean_instHashableMVarId_hash(v_x_2644_);
v___x_2646_ = lean_uint64_to_usize(v___x_2645_);
v___x_2647_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_2643_, v___x_2646_, v_x_2644_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_2648_, lean_object* v_x_2649_){
_start:
{
uint8_t v_res_2650_; lean_object* v_r_2651_; 
v_res_2650_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(v_x_2648_, v_x_2649_);
lean_dec(v_x_2649_);
lean_dec_ref(v_x_2648_);
v_r_2651_ = lean_box(v_res_2650_);
return v_r_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(lean_object* v_mvarId_2652_, lean_object* v___y_2653_){
_start:
{
lean_object* v___x_2655_; lean_object* v_mctx_2656_; lean_object* v_eAssignment_2657_; uint8_t v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2655_ = lean_st_ref_get(v___y_2653_);
v_mctx_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc_ref(v_mctx_2656_);
lean_dec(v___x_2655_);
v_eAssignment_2657_ = lean_ctor_get(v_mctx_2656_, 8);
lean_inc_ref(v_eAssignment_2657_);
lean_dec_ref(v_mctx_2656_);
v___x_2658_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(v_eAssignment_2657_, v_mvarId_2652_);
lean_dec_ref(v_eAssignment_2657_);
v___x_2659_ = lean_box(v___x_2658_);
v___x_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2659_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg___boxed(lean_object* v_mvarId_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(v_mvarId_2661_, v___y_2662_);
lean_dec(v___y_2662_);
lean_dec(v_mvarId_2661_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1(size_t v_sz_2665_, size_t v_i_2666_, lean_object* v_bs_2667_){
_start:
{
uint8_t v___x_2668_; 
v___x_2668_ = lean_usize_dec_lt(v_i_2666_, v_sz_2665_);
if (v___x_2668_ == 0)
{
return v_bs_2667_;
}
else
{
lean_object* v_v_2669_; lean_object* v_name_2670_; lean_object* v_type_2671_; lean_object* v_value_2672_; lean_object* v___x_2673_; lean_object* v_bs_x27_2674_; uint8_t v___x_2675_; uint8_t v___x_2676_; lean_object* v___x_2677_; size_t v___x_2678_; size_t v___x_2679_; lean_object* v___x_2680_; 
v_v_2669_ = lean_array_uget_borrowed(v_bs_2667_, v_i_2666_);
v_name_2670_ = lean_ctor_get(v_v_2669_, 0);
lean_inc(v_name_2670_);
v_type_2671_ = lean_ctor_get(v_v_2669_, 1);
lean_inc_ref(v_type_2671_);
v_value_2672_ = lean_ctor_get(v_v_2669_, 2);
lean_inc_ref(v_value_2672_);
v___x_2673_ = lean_unsigned_to_nat(0u);
v_bs_x27_2674_ = lean_array_uset(v_bs_2667_, v_i_2666_, v___x_2673_);
v___x_2675_ = 0;
v___x_2676_ = 0;
v___x_2677_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2677_, 0, v_name_2670_);
lean_ctor_set(v___x_2677_, 1, v_type_2671_);
lean_ctor_set(v___x_2677_, 2, v_value_2672_);
lean_ctor_set_uint8(v___x_2677_, sizeof(void*)*3, v___x_2675_);
lean_ctor_set_uint8(v___x_2677_, sizeof(void*)*3 + 1, v___x_2676_);
v___x_2678_ = ((size_t)1ULL);
v___x_2679_ = lean_usize_add(v_i_2666_, v___x_2678_);
v___x_2680_ = lean_array_uset(v_bs_x27_2674_, v_i_2666_, v___x_2677_);
v_i_2666_ = v___x_2679_;
v_bs_2667_ = v___x_2680_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1___boxed(lean_object* v_sz_2682_, lean_object* v_i_2683_, lean_object* v_bs_2684_){
_start:
{
size_t v_sz_boxed_2685_; size_t v_i_boxed_2686_; lean_object* v_res_2687_; 
v_sz_boxed_2685_ = lean_unbox_usize(v_sz_2682_);
lean_dec(v_sz_2682_);
v_i_boxed_2686_ = lean_unbox_usize(v_i_2683_);
lean_dec(v_i_2683_);
v_res_2687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1(v_sz_boxed_2685_, v_i_boxed_2686_, v_bs_2684_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize(lean_object* v_x_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_){
_start:
{
lean_object* v___x_2703_; uint8_t v___x_2704_; 
v___x_2703_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0));
lean_inc(v_x_2693_);
v___x_2704_ = l_Lean_Syntax_isOfKind(v_x_2693_, v___x_2703_);
if (v___x_2704_ == 0)
{
lean_object* v___x_2705_; 
lean_dec(v_x_2693_);
v___x_2705_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2705_;
}
else
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; uint8_t v___x_2709_; 
v___x_2706_ = lean_unsigned_to_nat(1u);
v___x_2707_ = l_Lean_Syntax_getArg(v_x_2693_, v___x_2706_);
v___x_2708_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_2707_);
v___x_2709_ = l_Lean_Syntax_isOfKind(v___x_2707_, v___x_2708_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; 
lean_dec(v___x_2707_);
lean_dec(v_x_2693_);
v___x_2710_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2710_;
}
else
{
lean_object* v___x_2711_; lean_object* v_types_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___x_2835_; lean_object* v___x_2836_; uint8_t v___x_2837_; 
v___x_2711_ = lean_unsigned_to_nat(0u);
v___x_2835_ = lean_unsigned_to_nat(2u);
v___x_2836_ = l_Lean_Syntax_getArg(v_x_2693_, v___x_2835_);
lean_dec(v_x_2693_);
v___x_2837_ = l_Lean_Syntax_isNone(v___x_2836_);
if (v___x_2837_ == 0)
{
uint8_t v___x_2838_; 
lean_inc(v___x_2836_);
v___x_2838_ = l_Lean_Syntax_matchesNull(v___x_2836_, v___x_2706_);
if (v___x_2838_ == 0)
{
lean_object* v___x_2839_; 
lean_dec(v___x_2836_);
lean_dec(v___x_2707_);
v___x_2839_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2839_;
}
else
{
lean_object* v_types_2840_; lean_object* v___x_2841_; uint8_t v___x_2842_; 
v_types_2840_ = l_Lean_Syntax_getArg(v___x_2836_, v___x_2711_);
lean_dec(v___x_2836_);
v___x_2841_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_types_2840_);
v___x_2842_ = l_Lean_Syntax_isOfKind(v_types_2840_, v___x_2841_);
if (v___x_2842_ == 0)
{
lean_object* v___x_2843_; 
lean_dec(v_types_2840_);
lean_dec(v___x_2707_);
v___x_2843_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2843_;
}
else
{
lean_object* v___x_2844_; 
v___x_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2844_, 0, v_types_2840_);
v_types_2713_ = v___x_2844_;
v___y_2714_ = v_a_2694_;
v___y_2715_ = v_a_2695_;
v___y_2716_ = v_a_2696_;
v___y_2717_ = v_a_2697_;
v___y_2718_ = v_a_2698_;
v___y_2719_ = v_a_2699_;
v___y_2720_ = v_a_2700_;
v___y_2721_ = v_a_2701_;
goto v___jp_2712_;
}
}
}
else
{
lean_object* v___x_2845_; 
lean_dec(v___x_2836_);
v___x_2845_ = lean_box(0);
v_types_2713_ = v___x_2845_;
v___y_2714_ = v_a_2694_;
v___y_2715_ = v_a_2695_;
v___y_2716_ = v_a_2696_;
v___y_2717_ = v_a_2697_;
v___y_2718_ = v_a_2698_;
v___y_2719_ = v_a_2699_;
v___y_2720_ = v_a_2700_;
v___y_2721_ = v_a_2701_;
goto v___jp_2712_;
}
v___jp_2712_:
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_2720_, v___y_2721_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2833_; 
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2833_ == 0)
{
lean_object* v_unused_2834_; 
v_unused_2834_ = lean_ctor_get(v___x_2722_, 0);
lean_dec(v_unused_2834_);
v___x_2724_ = v___x_2722_;
v_isShared_2725_ = v_isSharedCheck_2833_;
goto v_resetjp_2723_;
}
else
{
lean_dec(v___x_2722_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2833_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2726_; uint8_t v___x_2727_; lean_object* v___x_2728_; uint8_t v___x_2729_; lean_object* v___x_2730_; uint8_t v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2726_ = lean_unsigned_to_nat(10u);
v___x_2727_ = 0;
v___x_2728_ = lean_unsigned_to_nat(100000u);
v___x_2729_ = 0;
v___x_2730_ = lean_unsigned_to_nat(1000u);
v___x_2731_ = 1;
v___x_2732_ = lean_alloc_ctor(0, 3, 15);
lean_ctor_set(v___x_2732_, 0, v___x_2726_);
lean_ctor_set(v___x_2732_, 1, v___x_2728_);
lean_ctor_set(v___x_2732_, 2, v___x_2730_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*3, v___x_2709_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*3 + 1, v___x_2709_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*3 + 2, v___x_2727_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*3 + 3, v___x_2709_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*3 + 4, v___x_2709_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*3 + 5, v___x_2709_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*3 + 6, v___x_2709_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*3 + 7, v___x_2709_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*3 + 8, v___x_2727_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*3 + 9, v___x_2727_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*3 + 10, v___x_2729_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*3 + 11, v___x_2727_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*3 + 12, v___x_2727_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*3 + 13, v___x_2731_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*3 + 14, v___x_2709_);
v___x_2733_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_2707_, v___x_2732_, v___x_2709_, v___y_2714_, v___y_2720_, v___y_2721_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2734_; lean_object* v___x_2735_; 
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_a_2734_);
lean_dec_ref_known(v___x_2733_, 1);
v___x_2735_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_types_2713_, v_a_2734_, v___y_2720_, v___y_2721_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v___x_2737_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
lean_dec_ref_known(v___x_2735_, 1);
v___x_2737_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2715_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
lean_inc(v_a_2738_);
lean_dec_ref_known(v___x_2737_, 1);
v___x_2739_ = lean_unsigned_to_nat(1024u);
v___x_2740_ = lean_unsigned_to_nat(9u);
v___x_2741_ = lean_unsigned_to_nat(5u);
v___x_2742_ = lean_unsigned_to_nat(8u);
v___x_2743_ = lean_unsigned_to_nat(10000u);
v___x_2744_ = lean_unsigned_to_nat(16u);
v___x_2745_ = lean_unsigned_to_nat(1048576u);
v___x_2746_ = lean_unsigned_to_nat(50u);
v___x_2747_ = lean_box(0);
v___x_2748_ = lean_alloc_ctor(0, 18, 35);
lean_ctor_set(v___x_2748_, 0, v___x_2739_);
lean_ctor_set(v___x_2748_, 1, v___x_2740_);
lean_ctor_set(v___x_2748_, 2, v___x_2741_);
lean_ctor_set(v___x_2748_, 3, v___x_2742_);
lean_ctor_set(v___x_2748_, 4, v___x_2742_);
lean_ctor_set(v___x_2748_, 5, v___x_2730_);
lean_ctor_set(v___x_2748_, 6, v___x_2730_);
lean_ctor_set(v___x_2748_, 7, v___x_2711_);
lean_ctor_set(v___x_2748_, 8, v___x_2728_);
lean_ctor_set(v___x_2748_, 9, v___x_2739_);
lean_ctor_set(v___x_2748_, 10, v___x_2743_);
lean_ctor_set(v___x_2748_, 11, v___x_2742_);
lean_ctor_set(v___x_2748_, 12, v___x_2744_);
lean_ctor_set(v___x_2748_, 13, v___x_2730_);
lean_ctor_set(v___x_2748_, 14, v___x_2745_);
lean_ctor_set(v___x_2748_, 15, v___x_2726_);
lean_ctor_set(v___x_2748_, 16, v___x_2746_);
lean_ctor_set(v___x_2748_, 17, v___x_2747_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18, v___x_2727_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 1, v___x_2727_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 2, v___x_2727_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 3, v___x_2727_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 4, v___x_2727_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 5, v___x_2709_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 6, v___x_2709_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 7, v___x_2709_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 8, v___x_2727_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 9, v___x_2727_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 10, v___x_2727_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 11, v___x_2709_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 12, v___x_2727_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 13, v___x_2709_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 14, v___x_2709_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 15, v___x_2709_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 16, v___x_2727_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 17, v___x_2709_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 18, v___x_2727_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 19, v___x_2709_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 20, v___x_2709_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 21, v___x_2709_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 22, v___x_2727_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 23, v___x_2709_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 24, v___x_2709_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 25, v___x_2709_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 26, v___x_2709_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 27, v___x_2709_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 28, v___x_2709_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 29, v___x_2709_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 30, v___x_2709_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 31, v___x_2709_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 32, v___x_2727_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 33, v___x_2709_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*18 + 34, v___x_2709_);
v___x_2749_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_2748_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v___x_2752_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v___x_2749_, 1);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 0, v_a_2736_);
v___x_2752_ = v___x_2724_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2736_);
v___x_2752_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___f_2756_; lean_object* v___x_2757_; 
v___x_2753_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v___x_2752_, v_a_2734_, v___x_2747_);
v___x_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2754_, 0, v_a_2738_);
v___x_2755_ = lean_box(v___x_2727_);
v___f_2756_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0___boxed), 16, 6);
lean_closure_set(v___f_2756_, 0, v___x_2744_);
lean_closure_set(v___f_2756_, 1, v___x_2711_);
lean_closure_set(v___f_2756_, 2, v___x_2754_);
lean_closure_set(v___f_2756_, 3, v___x_2755_);
lean_closure_set(v___f_2756_, 4, v___x_2747_);
lean_closure_set(v___f_2756_, 5, v___x_2753_);
v___x_2757_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___f_2756_, v_a_2750_, v___x_2747_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; lean_object* v_snd_2759_; lean_object* v_target_2760_; lean_object* v_hypotheses_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v_a_2764_; uint8_t v___x_2765_; 
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
lean_inc(v_a_2758_);
lean_dec_ref_known(v___x_2757_, 1);
v_snd_2759_ = lean_ctor_get(v_a_2758_, 1);
lean_inc(v_snd_2759_);
lean_dec(v_a_2758_);
v_target_2760_ = lean_ctor_get(v_snd_2759_, 2);
lean_inc_ref(v_target_2760_);
v_hypotheses_2761_ = lean_ctor_get(v_snd_2759_, 3);
lean_inc_ref(v_hypotheses_2761_);
lean_dec(v_snd_2759_);
v___x_2762_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_2760_);
lean_dec_ref(v_target_2760_);
v___x_2763_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(v___x_2762_, v___y_2719_);
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_a_2764_);
lean_dec_ref(v___x_2763_);
v___x_2765_ = lean_unbox(v_a_2764_);
lean_dec(v_a_2764_);
if (v___x_2765_ == 0)
{
size_t v_sz_2766_; size_t v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v_sz_2766_ = lean_array_size(v_hypotheses_2761_);
v___x_2767_ = ((size_t)0ULL);
v___x_2768_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1(v_sz_2766_, v___x_2767_, v_hypotheses_2761_);
v___x_2769_ = l_Lean_MVarId_assertHypotheses(v___x_2762_, v___x_2768_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; lean_object* v_snd_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2780_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc(v_a_2770_);
lean_dec_ref_known(v___x_2769_, 1);
v_snd_2771_ = lean_ctor_get(v_a_2770_, 1);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_a_2770_);
if (v_isSharedCheck_2780_ == 0)
{
lean_object* v_unused_2781_; 
v_unused_2781_ = lean_ctor_get(v_a_2770_, 0);
lean_dec(v_unused_2781_);
v___x_2773_ = v_a_2770_;
v_isShared_2774_ = v_isSharedCheck_2780_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_snd_2771_);
lean_dec(v_a_2770_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2780_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2775_; lean_object* v___x_2777_; 
v___x_2775_ = lean_box(0);
if (v_isShared_2774_ == 0)
{
lean_ctor_set_tag(v___x_2773_, 1);
lean_ctor_set(v___x_2773_, 1, v___x_2775_);
lean_ctor_set(v___x_2773_, 0, v_snd_2771_);
v___x_2777_ = v___x_2773_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_snd_2771_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v___x_2775_);
v___x_2777_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
lean_object* v___x_2778_; 
v___x_2778_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2777_, v___y_2715_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
return v___x_2778_;
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
v_a_2782_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2769_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2769_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
else
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
lean_dec(v___x_2762_);
lean_dec_ref(v_hypotheses_2761_);
v___x_2790_ = lean_box(0);
v___x_2791_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2790_, v___y_2715_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
return v___x_2791_;
}
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
v_a_2792_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2757_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2757_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec(v_a_2738_);
lean_dec(v_a_2736_);
lean_dec(v_a_2734_);
lean_del_object(v___x_2724_);
v_a_2801_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2749_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2749_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_dec(v_a_2736_);
lean_dec(v_a_2734_);
lean_del_object(v___x_2724_);
v_a_2809_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2737_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2737_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
lean_dec(v_a_2734_);
lean_del_object(v___x_2724_);
v_a_2817_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2735_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2735_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_del_object(v___x_2724_);
lean_dec(v_types_2713_);
v_a_2825_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2733_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2733_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
}
else
{
lean_dec(v_types_2713_);
lean_dec(v___x_2707_);
return v___x_2722_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___boxed(lean_object* v_x_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Lean_Elab_Tactic_BVDecide_evalBVNormalize(v_x_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_);
lean_dec(v_a_2854_);
lean_dec_ref(v_a_2853_);
lean_dec(v_a_2852_);
lean_dec_ref(v_a_2851_);
lean_dec(v_a_2850_);
lean_dec_ref(v_a_2849_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0(lean_object* v_mvarId_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(v_mvarId_2857_, v___y_2863_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___boxed(lean_object* v_mvarId_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0(v_mvarId_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v_mvarId_2868_);
return v_res_2878_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0(lean_object* v_00_u03b2_2879_, lean_object* v_x_2880_, lean_object* v_x_2881_){
_start:
{
uint8_t v___x_2882_; 
v___x_2882_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(v_x_2880_, v_x_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2883_, lean_object* v_x_2884_, lean_object* v_x_2885_){
_start:
{
uint8_t v_res_2886_; lean_object* v_r_2887_; 
v_res_2886_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0(v_00_u03b2_2883_, v_x_2884_, v_x_2885_);
lean_dec(v_x_2885_);
lean_dec_ref(v_x_2884_);
v_r_2887_ = lean_box(v_res_2886_);
return v_r_2887_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2888_, lean_object* v_x_2889_, size_t v_x_2890_, lean_object* v_x_2891_){
_start:
{
uint8_t v___x_2892_; 
v___x_2892_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_2889_, v_x_2890_, v_x_2891_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2893_, lean_object* v_x_2894_, lean_object* v_x_2895_, lean_object* v_x_2896_){
_start:
{
size_t v_x_4075__boxed_2897_; uint8_t v_res_2898_; lean_object* v_r_2899_; 
v_x_4075__boxed_2897_ = lean_unbox_usize(v_x_2895_);
lean_dec(v_x_2895_);
v_res_2898_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1(v_00_u03b2_2893_, v_x_2894_, v_x_4075__boxed_2897_, v_x_2896_);
lean_dec(v_x_2896_);
lean_dec_ref(v_x_2894_);
v_r_2899_ = lean_box(v_res_2898_);
return v_r_2899_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2900_, lean_object* v_keys_2901_, lean_object* v_vals_2902_, lean_object* v_heq_2903_, lean_object* v_i_2904_, lean_object* v_k_2905_){
_start:
{
uint8_t v___x_2906_; 
v___x_2906_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2901_, v_i_2904_, v_k_2905_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2907_, lean_object* v_keys_2908_, lean_object* v_vals_2909_, lean_object* v_heq_2910_, lean_object* v_i_2911_, lean_object* v_k_2912_){
_start:
{
uint8_t v_res_2913_; lean_object* v_r_2914_; 
v_res_2913_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2907_, v_keys_2908_, v_vals_2909_, v_heq_2910_, v_i_2911_, v_k_2912_);
lean_dec(v_k_2912_);
lean_dec_ref(v_vals_2909_);
lean_dec_ref(v_keys_2908_);
v_r_2914_ = lean_box(v_res_2913_);
return v_r_2914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1(){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2923_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2924_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0));
v___x_2925_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___closed__1));
v___x_2926_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___boxed), 10, 0);
v___x_2927_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2923_, v___x_2924_, v___x_2925_, v___x_2926_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___boxed(lean_object* v_a_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1();
return v_res_2929_;
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
