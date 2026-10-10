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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkDefaultParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
lean_object* lean_array_uget(lean_object*, size_t);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_4_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_5_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__1);
v___x_6_ = lean_unsigned_to_nat(0u);
v___x_7_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
lean_ctor_set(v___x_7_, 1, v___x_6_);
lean_ctor_set(v___x_7_, 2, v___x_6_);
lean_ctor_set(v___x_7_, 3, v___x_6_);
lean_ctor_set(v___x_7_, 4, v___x_5_);
lean_ctor_set(v___x_7_, 5, v___x_5_);
lean_ctor_set(v___x_7_, 6, v___x_5_);
lean_ctor_set(v___x_7_, 7, v___x_5_);
lean_ctor_set(v___x_7_, 8, v___x_5_);
lean_ctor_set(v___x_7_, 9, v___x_5_);
lean_ctor_set(v___x_7_, 10, v___x_5_);
lean_ctor_set(v___x_7_, 11, v___x_4_);
return v___x_7_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = lean_unsigned_to_nat(32u);
v___x_9_ = lean_mk_empty_array_with_capacity(v___x_8_);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_11_ = ((size_t)5ULL);
v___x_12_ = lean_unsigned_to_nat(0u);
v___x_13_ = lean_unsigned_to_nat(32u);
v___x_14_ = lean_mk_empty_array_with_capacity(v___x_13_);
v___x_15_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__3);
v___x_16_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___x_14_);
lean_ctor_set(v___x_16_, 2, v___x_12_);
lean_ctor_set(v___x_16_, 3, v___x_12_);
lean_ctor_set_usize(v___x_16_, 4, v___x_11_);
return v___x_16_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_17_ = lean_box(1);
v___x_18_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__4);
v___x_19_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__1);
v___x_20_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
lean_ctor_set(v___x_20_, 1, v___x_18_);
lean_ctor_set(v___x_20_, 2, v___x_17_);
return v___x_20_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0(lean_object* v_msgData_21_, lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
lean_object* v___x_25_; lean_object* v_toCold_26_; lean_object* v_env_27_; lean_object* v_options_28_; uint8_t v___x_29_; lean_object* v_env_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_25_ = lean_st_ref_get(v___y_23_);
v_toCold_26_ = lean_ctor_get(v___y_22_, 0);
v_env_27_ = lean_ctor_get(v___x_25_, 0);
lean_inc_ref(v_env_27_);
lean_dec(v___x_25_);
v_options_28_ = lean_ctor_get(v_toCold_26_, 2);
v___x_29_ = 0;
v_env_30_ = l_Lean_Environment_setRecordingDeps(v_env_27_, v___x_29_);
v___x_31_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__2);
v___x_32_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_28_);
v___x_33_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_33_, 0, v_env_30_);
lean_ctor_set(v___x_33_, 1, v___x_31_);
lean_ctor_set(v___x_33_, 2, v___x_32_);
lean_ctor_set(v___x_33_, 3, v_options_28_);
v___x_34_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
lean_ctor_set(v___x_34_, 1, v_msgData_21_);
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_21_ = stack[0].m_obj;
lean_object* v___y_22_ = stack[1].m_obj;
lean_object* v___y_23_ = stack[2].m_obj;
lean_object* v_res_36_;
v_res_36_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0(v_msgData_21_, v___y_22_, v___y_23_);
stack->m_obj
 = v_res_36_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___boxed(lean_object* v_msgData_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0(v_msgData_37_, v___y_38_, v___y_39_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
return v_res_41_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg(lean_object* v_msg_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_ref_46_; lean_object* v___x_47_; lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_56_; 
v_ref_46_ = lean_ctor_get(v___y_43_, 2);
v___x_47_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0(v_msg_42_, v___y_43_, v___y_44_);
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
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_42_ = stack[0].m_obj;
lean_object* v___y_43_ = stack[1].m_obj;
lean_object* v___y_44_ = stack[2].m_obj;
lean_object* v_res_57_;
v_res_57_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg(v_msg_42_, v___y_43_, v___y_44_);
stack->m_obj
 = v_res_57_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg___boxed(lean_object* v_msg_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg(v_msg_58_, v___y_59_, v___y_60_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
return v_res_62_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__5(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__4));
v___x_72_ = l_Lean_stringToMessageData(v___x_71_);
return v___x_72_;
}
}
lean_object* l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v___x_76_; lean_object* v_env_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_76_ = lean_st_ref_get(v_a_74_);
v_env_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc_ref(v_env_77_);
lean_dec(v___x_76_);
v___x_78_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__3));
v___x_79_ = l_Lean_Environment_getModuleIdx_x3f(v_env_77_, v___x_78_);
lean_dec_ref(v_env_77_);
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__5, &l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__5);
v___x_81_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg(v___x_80_, v_a_73_, v_a_74_);
return v___x_81_;
}
else
{
lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_89_; 
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_89_ == 0)
{
lean_object* v_unused_90_; 
v_unused_90_ = lean_ctor_get(v___x_79_, 0);
lean_dec(v_unused_90_);
v___x_83_ = v___x_79_;
v_isShared_84_ = v_isSharedCheck_89_;
goto v_resetjp_82_;
}
else
{
lean_dec(v___x_79_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_89_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_85_ = lean_box(0);
if (v_isShared_84_ == 0)
{
lean_ctor_set_tag(v___x_83_, 0);
lean_ctor_set(v___x_83_, 0, v___x_85_);
v___x_87_ = v___x_83_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_ensureBvDecide_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_73_ = stack[0].m_obj;
lean_object* v_a_74_ = stack[1].m_obj;
lean_object* v_res_91_;
v_res_91_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v_a_73_, v_a_74_);
stack->m_obj
 = v_res_91_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___boxed(lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v_a_92_, v_a_93_);
lean_dec(v_a_93_);
lean_dec_ref(v_a_92_);
return v_res_95_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0(lean_object* v_00_u03b1_96_, lean_object* v_msg_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg(v_msg_97_, v___y_98_, v___y_99_);
return v___x_101_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_97_ = stack[1].m_obj;
lean_object* v___y_98_ = stack[2].m_obj;
lean_object* v___y_99_ = stack[3].m_obj;
lean_object* v_res_102_;
v_res_102_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0(lean_box(0), v_msg_97_, v___y_98_, v___y_99_);
stack->m_obj
 = v_res_102_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___boxed(lean_object* v_00_u03b1_103_, lean_object* v_msg_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0(v_00_u03b1_103_, v_msg_104_, v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
return v_res_108_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(lean_object* v_msgData_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v___x_115_; lean_object* v_env_116_; uint8_t v___x_117_; lean_object* v_env_118_; lean_object* v___x_119_; lean_object* v_toCold_120_; lean_object* v_mctx_121_; lean_object* v_lctx_122_; lean_object* v_options_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_115_ = lean_st_ref_get(v___y_113_);
v_env_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc_ref(v_env_116_);
lean_dec(v___x_115_);
v___x_117_ = 0;
v_env_118_ = l_Lean_Environment_setRecordingDeps(v_env_116_, v___x_117_);
v___x_119_ = lean_st_ref_get(v___y_111_);
v_toCold_120_ = lean_ctor_get(v___y_112_, 0);
v_mctx_121_ = lean_ctor_get(v___x_119_, 0);
lean_inc_ref(v_mctx_121_);
lean_dec(v___x_119_);
v_lctx_122_ = lean_ctor_get(v___y_110_, 2);
v_options_123_ = lean_ctor_get(v_toCold_120_, 2);
lean_inc_ref(v_options_123_);
lean_inc_ref(v_lctx_122_);
v___x_124_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_124_, 0, v_env_118_);
lean_ctor_set(v___x_124_, 1, v_mctx_121_);
lean_ctor_set(v___x_124_, 2, v_lctx_122_);
lean_ctor_set(v___x_124_, 3, v_options_123_);
v___x_125_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v_msgData_109_);
v___x_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_109_ = stack[0].m_obj;
lean_object* v___y_110_ = stack[1].m_obj;
lean_object* v___y_111_ = stack[2].m_obj;
lean_object* v___y_112_ = stack[3].m_obj;
lean_object* v___y_113_ = stack[4].m_obj;
lean_object* v_res_127_;
v_res_127_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v_msgData_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
stack->m_obj
 = v_res_127_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0___boxed(lean_object* v_msgData_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v_msgData_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
return v_res_134_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_box(1);
v___x_136_ = l_Lean_MessageData_ofFormat(v___x_135_);
return v___x_136_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__2));
v___x_141_ = l_Lean_MessageData_ofFormat(v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3(lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
if (lean_obj_tag(v_x_143_) == 0)
{
return v_x_142_;
}
else
{
lean_object* v_head_144_; lean_object* v_tail_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_167_; 
v_head_144_ = lean_ctor_get(v_x_143_, 0);
v_tail_145_ = lean_ctor_get(v_x_143_, 1);
v_isSharedCheck_167_ = !lean_is_exclusive(v_x_143_);
if (v_isSharedCheck_167_ == 0)
{
v___x_147_ = v_x_143_;
v_isShared_148_ = v_isSharedCheck_167_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_tail_145_);
lean_inc(v_head_144_);
lean_dec(v_x_143_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_167_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v_before_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_165_; 
v_before_149_ = lean_ctor_get(v_head_144_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v_head_144_);
if (v_isSharedCheck_165_ == 0)
{
lean_object* v_unused_166_; 
v_unused_166_ = lean_ctor_get(v_head_144_, 1);
lean_dec(v_unused_166_);
v___x_151_ = v_head_144_;
v_isShared_152_ = v_isSharedCheck_165_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_before_149_);
lean_dec(v_head_144_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_165_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_153_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_152_ == 0)
{
lean_ctor_set_tag(v___x_151_, 7);
lean_ctor_set(v___x_151_, 1, v___x_153_);
lean_ctor_set(v___x_151_, 0, v_x_142_);
v___x_155_ = v___x_151_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_x_142_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v___x_153_);
v___x_155_ = v_reuseFailAlloc_164_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_156_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_148_ == 0)
{
lean_ctor_set_tag(v___x_147_, 7);
lean_ctor_set(v___x_147_, 1, v___x_156_);
lean_ctor_set(v___x_147_, 0, v___x_155_);
v___x_158_ = v___x_147_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_155_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v___x_156_);
v___x_158_ = v_reuseFailAlloc_163_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = l_Lean_MessageData_ofSyntax(v_before_149_);
v___x_160_ = l_Lean_indentD(v___x_159_);
v___x_161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_158_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v_x_142_ = v___x_161_;
v_x_143_ = v_tail_145_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(lean_object* v_opts_168_, lean_object* v_opt_169_){
_start:
{
lean_object* v_name_170_; lean_object* v_defValue_171_; lean_object* v_map_172_; lean_object* v___x_173_; 
v_name_170_ = lean_ctor_get(v_opt_169_, 0);
v_defValue_171_ = lean_ctor_get(v_opt_169_, 1);
v_map_172_ = lean_ctor_get(v_opts_168_, 0);
v___x_173_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_172_, v_name_170_);
if (lean_obj_tag(v___x_173_) == 0)
{
uint8_t v___x_174_; 
v___x_174_ = lean_unbox(v_defValue_171_);
return v___x_174_;
}
else
{
lean_object* v_val_175_; 
v_val_175_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_val_175_);
lean_dec_ref_known(v___x_173_, 1);
if (lean_obj_tag(v_val_175_) == 1)
{
uint8_t v_v_176_; 
v_v_176_ = lean_ctor_get_uint8(v_val_175_, 0);
lean_dec_ref_known(v_val_175_, 0);
return v_v_176_;
}
else
{
uint8_t v___x_177_; 
lean_dec(v_val_175_);
v___x_177_ = lean_unbox(v_defValue_171_);
return v___x_177_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_168_ = stack[0].m_obj;
lean_object* v_opt_169_ = stack[1].m_obj;
uint8_t v_res_178_;
v_res_178_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_opts_168_, v_opt_169_);
stack->m_num = v_res_178_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_179_, lean_object* v_opt_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_opts_179_, v_opt_180_);
lean_dec_ref(v_opt_180_);
lean_dec_ref(v_opts_179_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__1));
v___x_187_ = l_Lean_MessageData_ofFormat(v___x_186_);
return v___x_187_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(lean_object* v_msgData_188_, lean_object* v_macroStack_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_192_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_190_);
v___x_193_ = l_Lean_Elab_pp_macroStack;
v___x_194_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v___x_192_, v___x_193_);
lean_dec_ref(v___x_192_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
lean_dec(v_macroStack_189_);
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v_msgData_188_);
return v___x_195_;
}
else
{
if (lean_obj_tag(v_macroStack_189_) == 0)
{
lean_object* v___x_196_; 
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v_msgData_188_);
return v___x_196_;
}
else
{
lean_object* v_head_197_; lean_object* v_after_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_213_; 
v_head_197_ = lean_ctor_get(v_macroStack_189_, 0);
lean_inc(v_head_197_);
v_after_198_ = lean_ctor_get(v_head_197_, 1);
v_isSharedCheck_213_ = !lean_is_exclusive(v_head_197_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; 
v_unused_214_ = lean_ctor_get(v_head_197_, 0);
lean_dec(v_unused_214_);
v___x_200_ = v_head_197_;
v_isShared_201_ = v_isSharedCheck_213_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_after_198_);
lean_dec(v_head_197_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_213_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_202_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_201_ == 0)
{
lean_ctor_set_tag(v___x_200_, 7);
lean_ctor_set(v___x_200_, 1, v___x_202_);
lean_ctor_set(v___x_200_, 0, v_msgData_188_);
v___x_204_ = v___x_200_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_msgData_188_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_202_);
v___x_204_ = v_reuseFailAlloc_212_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v_msgData_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_205_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2);
v___x_206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_204_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v___x_207_ = l_Lean_MessageData_ofSyntax(v_after_198_);
v___x_208_ = l_Lean_indentD(v___x_207_);
v_msgData_209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_209_, 0, v___x_206_);
lean_ctor_set(v_msgData_209_, 1, v___x_208_);
v___x_210_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3(v_msgData_209_, v_macroStack_189_);
v___x_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
return v___x_211_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_188_ = stack[0].m_obj;
lean_object* v_macroStack_189_ = stack[1].m_obj;
lean_object* v___y_190_ = stack[2].m_obj;
lean_object* v_res_215_;
v_res_215_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_msgData_188_, v_macroStack_189_, v___y_190_);
stack->m_obj
 = v_res_215_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_216_, lean_object* v_macroStack_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_msgData_216_, v_macroStack_217_, v___y_218_);
lean_dec_ref(v___y_218_);
return v_res_220_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(lean_object* v_msg_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_ref_229_; lean_object* v_macroStack_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v_a_233_; lean_object* v___x_234_; lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_243_; 
v_ref_229_ = lean_ctor_get(v___y_226_, 2);
v_macroStack_230_ = lean_ctor_get(v___y_222_, 1);
v___x_231_ = l_Lean_Elab_getBetterRef(v_ref_229_, v_macroStack_230_);
v___x_232_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v_msg_221_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
v_a_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_a_233_);
lean_dec_ref(v___x_232_);
lean_inc(v_macroStack_230_);
v___x_234_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_a_233_, v_macroStack_230_, v___y_226_);
v_a_235_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_243_ == 0)
{
v___x_237_ = v___x_234_;
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_231_);
lean_ctor_set(v___x_239_, 1, v_a_235_);
if (v_isShared_238_ == 0)
{
lean_ctor_set_tag(v___x_237_, 1);
lean_ctor_set(v___x_237_, 0, v___x_239_);
v___x_241_ = v___x_237_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_221_ = stack[0].m_obj;
lean_object* v___y_222_ = stack[1].m_obj;
lean_object* v___y_223_ = stack[2].m_obj;
lean_object* v___y_224_ = stack[3].m_obj;
lean_object* v___y_225_ = stack[4].m_obj;
lean_object* v___y_226_ = stack[5].m_obj;
lean_object* v___y_227_ = stack[6].m_obj;
lean_object* v_res_244_;
v_res_244_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v_msg_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
stack->m_obj
 = v_res_244_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg___boxed(lean_object* v_msg_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v_msg_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
return v_res_253_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__0));
v___x_256_ = l_Lean_stringToMessageData(v___x_255_);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__2));
v___x_259_ = l_Lean_stringToMessageData(v___x_258_);
return v___x_259_;
}
}
lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_toCold_267_; lean_object* v_fileName_268_; lean_object* v___x_269_; 
v_toCold_267_ = lean_ctor_get(v_a_264_, 0);
v_fileName_268_ = lean_ctor_get(v_toCold_267_, 0);
lean_inc_ref(v_fileName_268_);
v___x_269_ = l_System_FilePath_parent(v_fileName_268_);
if (lean_obj_tag(v___x_269_) == 1)
{
lean_object* v_val_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
v_val_270_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_269_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_val_270_);
lean_dec(v___x_269_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
lean_ctor_set_tag(v___x_272_, 0);
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_val_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
lean_dec(v___x_269_);
v___x_278_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1, &l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1);
lean_inc_ref(v_fileName_268_);
v___x_279_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_279_, 0, v_fileName_268_);
v___x_280_ = l_Lean_MessageData_ofFormat(v___x_279_);
v___x_281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_278_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3, &l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3);
v___x_283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_281_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v___x_283_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
return v___x_284_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_260_ = stack[0].m_obj;
lean_object* v_a_261_ = stack[1].m_obj;
lean_object* v_a_262_ = stack[2].m_obj;
lean_object* v_a_263_ = stack[3].m_obj;
lean_object* v_a_264_ = stack[4].m_obj;
lean_object* v_a_265_ = stack[5].m_obj;
lean_object* v_res_285_;
v_res_285_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
stack->m_obj
 = v_res_285_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___boxed(lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
return v_res_293_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0(lean_object* v_00_u03b1_294_, lean_object* v_msg_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v_msg_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
return v___x_303_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_295_ = stack[1].m_obj;
lean_object* v___y_296_ = stack[2].m_obj;
lean_object* v___y_297_ = stack[3].m_obj;
lean_object* v___y_298_ = stack[4].m_obj;
lean_object* v___y_299_ = stack[5].m_obj;
lean_object* v___y_300_ = stack[6].m_obj;
lean_object* v___y_301_ = stack[7].m_obj;
lean_object* v_res_304_;
v_res_304_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0(lean_box(0), v_msg_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
stack->m_obj
 = v_res_304_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___boxed(lean_object* v_00_u03b1_305_, lean_object* v_msg_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0(v_00_u03b1_305_, v_msg_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
return v_res_314_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1(lean_object* v_msgData_315_, lean_object* v_macroStack_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_msgData_315_, v_macroStack_316_, v___y_321_);
return v___x_324_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_315_ = stack[0].m_obj;
lean_object* v_macroStack_316_ = stack[1].m_obj;
lean_object* v___y_317_ = stack[2].m_obj;
lean_object* v___y_318_ = stack[3].m_obj;
lean_object* v___y_319_ = stack[4].m_obj;
lean_object* v___y_320_ = stack[5].m_obj;
lean_object* v___y_321_ = stack[6].m_obj;
lean_object* v___y_322_ = stack[7].m_obj;
lean_object* v_res_325_;
v_res_325_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1(v_msgData_315_, v_macroStack_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
stack->m_obj
 = v_res_325_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___boxed(lean_object* v_msgData_326_, lean_object* v_macroStack_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1(v_msgData_326_, v_macroStack_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
return v_res_335_;
}
}
lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(lean_object* v_lratPath_336_, lean_object* v_cfg_337_, lean_object* v_types_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_a_347_);
lean_dec_ref_known(v___x_346_, 1);
v___x_348_ = l_System_FilePath_join(v_a_347_, v_lratPath_336_);
v___x_349_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new(v___x_348_, v_cfg_337_, v_types_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
return v___x_349_;
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec(v_types_338_);
lean_dec_ref(v_cfg_337_);
lean_dec_ref(v_lratPath_336_);
v_a_350_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_346_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_346_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext_0interp(lean_interpreter_value* stack)
{
lean_object* v_lratPath_336_ = stack[0].m_obj;
lean_object* v_cfg_337_ = stack[1].m_obj;
lean_object* v_types_338_ = stack[2].m_obj;
lean_object* v_a_339_ = stack[3].m_obj;
lean_object* v_a_340_ = stack[4].m_obj;
lean_object* v_a_341_ = stack[5].m_obj;
lean_object* v_a_342_ = stack[6].m_obj;
lean_object* v_a_343_ = stack[7].m_obj;
lean_object* v_a_344_ = stack[8].m_obj;
lean_object* v_res_358_;
v_res_358_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v_lratPath_336_, v_cfg_337_, v_types_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
stack->m_obj
 = v_res_358_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext___boxed(lean_object* v_lratPath_359_, lean_object* v_cfg_360_, lean_object* v_types_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v_lratPath_359_, v_cfg_360_, v_types_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
return v_res_369_;
}
}
lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0(lean_object* v_g_370_, lean_object* v___x_371_, lean_object* v___x_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(v_g_370_, v___x_371_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_392_ == 0)
{
lean_object* v_unused_393_; 
v_unused_393_ = lean_ctor_get(v___x_385_, 0);
lean_dec(v_unused_393_);
v___x_387_ = v___x_385_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_dec(v___x_385_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v___x_372_);
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_372_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
v_a_394_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_385_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_385_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_370_ = stack[0].m_obj;
lean_object* v___x_371_ = stack[1].m_obj;
lean_object* v___x_372_ = stack[2].m_obj;
lean_object* v___y_373_ = stack[3].m_obj;
lean_object* v___y_374_ = stack[4].m_obj;
lean_object* v___y_375_ = stack[5].m_obj;
lean_object* v___y_376_ = stack[6].m_obj;
lean_object* v___y_377_ = stack[7].m_obj;
lean_object* v___y_378_ = stack[8].m_obj;
lean_object* v___y_379_ = stack[9].m_obj;
lean_object* v___y_380_ = stack[10].m_obj;
lean_object* v___y_381_ = stack[11].m_obj;
lean_object* v___y_382_ = stack[12].m_obj;
lean_object* v___y_383_ = stack[13].m_obj;
lean_object* v_res_402_;
v_res_402_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0(v_g_370_, v___x_371_, v___x_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
stack->m_obj
 = v_res_402_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0___boxed(lean_object* v_g_403_, lean_object* v___x_404_, lean_object* v___x_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0(v_g_403_, v___x_404_, v___x_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
return v_res_418_;
}
}
lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(lean_object* v_g_419_, lean_object* v_hypotheses_420_, lean_object* v_ctx_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_config_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___f_435_; lean_object* v___x_436_; 
v_config_432_ = lean_ctor_get(v_ctx_421_, 5);
lean_inc_ref(v_config_432_);
v___x_433_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed), 16, 1);
lean_closure_set(v___x_433_, 0, v_ctx_421_);
v___x_434_ = lean_box(0);
v___f_435_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0___boxed), 15, 3);
lean_closure_set(v___f_435_, 0, v_g_419_);
lean_closure_set(v___f_435_, 1, v___x_433_);
lean_closure_set(v___f_435_, 2, v___x_434_);
v___x_436_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg(v___f_435_, v_hypotheses_420_, v_config_432_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
return v___x_436_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_419_ = stack[0].m_obj;
lean_object* v_hypotheses_420_ = stack[1].m_obj;
lean_object* v_ctx_421_ = stack[2].m_obj;
lean_object* v_a_422_ = stack[3].m_obj;
lean_object* v_a_423_ = stack[4].m_obj;
lean_object* v_a_424_ = stack[5].m_obj;
lean_object* v_a_425_ = stack[6].m_obj;
lean_object* v_a_426_ = stack[7].m_obj;
lean_object* v_a_427_ = stack[8].m_obj;
lean_object* v_a_428_ = stack[9].m_obj;
lean_object* v_a_429_ = stack[10].m_obj;
lean_object* v_a_430_ = stack[11].m_obj;
lean_object* v_res_437_;
v_res_437_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(v_g_419_, v_hypotheses_420_, v_ctx_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
stack->m_obj
 = v_res_437_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___boxed(lean_object* v_g_438_, lean_object* v_hypotheses_439_, lean_object* v_ctx_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(v_g_438_, v_hypotheses_439_, v_ctx_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec(v_a_441_);
return v_res_451_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__0);
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0);
v___x_455_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
lean_ctor_set(v___x_455_, 2, v___x_454_);
lean_ctor_set(v___x_455_, 3, v___x_454_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_456_ = lean_box(0);
v___x_457_ = lean_unsigned_to_nat(16u);
v___x_458_ = lean_mk_array(v___x_457_, v___x_456_);
return v___x_458_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2);
v___x_460_ = lean_unsigned_to_nat(0u);
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set(v___x_461_, 1, v___x_459_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3);
v___x_463_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
lean_ctor_set(v___x_463_, 2, v___x_462_);
lean_ctor_set(v___x_463_, 3, v___x_462_);
return v___x_463_;
}
}
lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck(lean_object* v_target_466_, lean_object* v_ctx_467_, lean_object* v_warn_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___y_488_; lean_object* v___x_498_; 
lean_inc_ref(v_ctx_467_);
v___x_479_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_ctx_467_);
v___x_480_ = lean_box(0);
v___x_481_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1);
v___x_482_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4);
v___x_483_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5));
v___x_484_ = 0;
v___x_485_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_485_, 0, v___x_481_);
lean_ctor_set(v___x_485_, 1, v___x_482_);
lean_ctor_set(v___x_485_, 2, v_target_466_);
lean_ctor_set(v___x_485_, 3, v___x_483_);
lean_ctor_set_uint8(v___x_485_, sizeof(void*)*4, v___x_484_);
v___x_486_ = lean_st_mk_ref(v___x_485_);
v___x_498_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_480_, v___x_479_, v___x_486_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
lean_dec_ref(v___x_479_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; uint8_t v___x_500_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref_known(v___x_498_, 1);
v___x_500_ = lean_unbox(v_a_499_);
lean_dec(v_a_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; lean_object* v_target_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v_hypotheses_505_; lean_object* v___x_506_; 
lean_dec_ref(v_warn_468_);
v___x_501_ = lean_st_ref_get(v___x_486_);
v_target_502_ = lean_ctor_get(v___x_501_, 2);
lean_inc_ref(v_target_502_);
lean_dec(v___x_501_);
v___x_503_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_502_);
lean_dec_ref(v_target_502_);
v___x_504_ = lean_st_ref_get(v___x_486_);
v_hypotheses_505_ = lean_ctor_get(v___x_504_, 3);
lean_inc_ref(v_hypotheses_505_);
lean_dec(v___x_504_);
v___x_506_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(v___x_503_, v_hypotheses_505_, v_ctx_467_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
v___y_488_ = v___x_506_;
goto v___jp_487_;
}
else
{
lean_object* v___x_507_; 
lean_dec_ref(v_ctx_467_);
lean_inc(v_a_477_);
lean_inc_ref(v_a_476_);
lean_inc(v_a_475_);
lean_inc_ref(v_a_474_);
v___x_507_ = lean_apply_5(v_warn_468_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, lean_box(0));
v___y_488_ = v___x_507_;
goto v___jp_487_;
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec(v___x_486_);
lean_dec_ref(v_warn_468_);
lean_dec_ref(v_ctx_467_);
v_a_508_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_498_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_498_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
v___jp_487_:
{
if (lean_obj_tag(v___y_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_497_; 
v_a_489_ = lean_ctor_get(v___y_488_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___y_488_);
if (v_isSharedCheck_497_ == 0)
{
v___x_491_ = v___y_488_;
v_isShared_492_ = v_isSharedCheck_497_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___y_488_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_497_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_493_ = lean_st_ref_get(v___x_486_);
lean_dec(v___x_486_);
lean_dec(v___x_493_);
if (v_isShared_492_ == 0)
{
v___x_495_ = v___x_491_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_489_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
else
{
lean_dec(v___x_486_);
return v___y_488_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_0interp(lean_interpreter_value* stack)
{
lean_object* v_target_466_ = stack[0].m_obj;
lean_object* v_ctx_467_ = stack[1].m_obj;
lean_object* v_warn_468_ = stack[2].m_obj;
lean_object* v_a_469_ = stack[3].m_obj;
lean_object* v_a_470_ = stack[4].m_obj;
lean_object* v_a_471_ = stack[5].m_obj;
lean_object* v_a_472_ = stack[6].m_obj;
lean_object* v_a_473_ = stack[7].m_obj;
lean_object* v_a_474_ = stack[8].m_obj;
lean_object* v_a_475_ = stack[9].m_obj;
lean_object* v_a_476_ = stack[10].m_obj;
lean_object* v_a_477_ = stack[11].m_obj;
lean_object* v_res_516_;
v_res_516_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck(v_target_466_, v_ctx_467_, v_warn_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
stack->m_obj
 = v_res_516_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed(lean_object* v_target_517_, lean_object* v_ctx_518_, lean_object* v_warn_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck(v_target_517_, v_ctx_518_, v_warn_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
return v_res_530_;
}
}
lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(lean_object* v___y_531_){
_start:
{
lean_object* v_ref_533_; uint8_t v___x_534_; lean_object* v___x_535_; 
v_ref_533_ = lean_ctor_get(v___y_531_, 2);
v___x_534_ = 0;
v___x_535_ = l_Lean_Syntax_getPos_x3f(v_ref_533_, v___x_534_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = lean_unsigned_to_nat(0u);
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
else
{
lean_object* v_val_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
v_val_538_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_535_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_val_538_);
lean_dec(v___x_535_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
lean_ctor_set_tag(v___x_540_, 0);
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_val_538_);
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
LEAN_EXPORT void l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_531_ = stack[0].m_obj;
lean_object* v_res_546_;
v_res_546_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v___y_531_);
stack->m_obj
 = v_res_546_;
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg___boxed(lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v___y_547_);
lean_dec_ref(v___y_547_);
return v_res_549_;
}
}
lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0(lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v___y_554_);
return v___x_557_;
}
}
LEAN_EXPORT void l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_550_ = stack[0].m_obj;
lean_object* v___y_551_ = stack[1].m_obj;
lean_object* v___y_552_ = stack[2].m_obj;
lean_object* v___y_553_ = stack[3].m_obj;
lean_object* v___y_554_ = stack[4].m_obj;
lean_object* v___y_555_ = stack[5].m_obj;
lean_object* v_res_558_;
v_res_558_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0(v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
stack->m_obj
 = v_res_558_;
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___boxed(lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0(v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
return v_res_566_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__2));
v___x_571_ = l_Lean_stringToMessageData(v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__4));
v___x_574_ = l_Lean_stringToMessageData(v___x_573_);
return v___x_574_;
}
}
lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v_toCold_582_; lean_object* v_fileName_583_; lean_object* v_fileMap_584_; lean_object* v___x_585_; 
v_toCold_582_ = lean_ctor_get(v_a_579_, 0);
v_fileName_583_ = lean_ctor_get(v_toCold_582_, 0);
v_fileMap_584_ = lean_ctor_get(v_toCold_582_, 1);
lean_inc_ref(v_fileName_583_);
v___x_585_ = l_System_FilePath_fileName(v_fileName_583_);
if (lean_obj_tag(v___x_585_) == 1)
{
lean_object* v_val_586_; lean_object* v___x_587_; 
v_val_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_val_586_);
lean_dec_ref_known(v___x_585_, 1);
v___x_587_ = l_Lean_Elab_Term_getDeclName_x3f___redArg(v_a_575_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_587_, 1);
if (lean_obj_tag(v_a_588_) == 1)
{
lean_object* v_val_589_; lean_object* v___x_590_; lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_614_; 
v_val_589_ = lean_ctor_get(v_a_588_, 0);
lean_inc(v_val_589_);
lean_dec_ref_known(v_a_588_, 1);
v___x_590_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v_a_579_);
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_614_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v_line_596_; lean_object* v_column_597_; lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_612_; 
lean_inc_ref(v_fileMap_584_);
v___x_595_ = l_Lean_FileMap_toPosition(v_fileMap_584_, v_a_591_);
lean_dec(v_a_591_);
v_line_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_line_596_);
v_column_597_ = lean_ctor_get(v___x_595_, 1);
lean_inc(v_column_597_);
lean_dec_ref(v___x_595_);
v___x_598_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__0));
v___x_599_ = lean_string_append(v_val_586_, v___x_598_);
v___x_600_ = 1;
v___x_601_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_589_, v___x_600_);
v___x_602_ = lean_string_append(v___x_599_, v___x_601_);
lean_dec_ref(v___x_601_);
v___x_603_ = lean_string_append(v___x_602_, v___x_598_);
v___x_604_ = l_Nat_reprFast(v_line_596_);
v___x_605_ = lean_string_append(v___x_603_, v___x_604_);
lean_dec_ref(v___x_604_);
v___x_606_ = lean_string_append(v___x_605_, v___x_598_);
v___x_607_ = l_Nat_reprFast(v_column_597_);
v___x_608_ = lean_string_append(v___x_606_, v___x_607_);
lean_dec_ref(v___x_607_);
v___x_609_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__1));
v___x_610_ = lean_string_append(v___x_608_, v___x_609_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_610_);
v___x_612_ = v___x_593_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
else
{
lean_object* v___x_615_; lean_object* v___x_616_; 
lean_dec(v_a_588_);
lean_dec(v_val_586_);
v___x_615_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3, &l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3);
v___x_616_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v___x_615_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
return v___x_616_;
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_dec(v_val_586_);
v_a_617_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_587_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_587_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec(v___x_585_);
v___x_625_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5, &l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5);
v___x_626_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v___x_625_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
return v___x_626_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_575_ = stack[0].m_obj;
lean_object* v_a_576_ = stack[1].m_obj;
lean_object* v_a_577_ = stack[2].m_obj;
lean_object* v_a_578_ = stack[3].m_obj;
lean_object* v_a_579_ = stack[4].m_obj;
lean_object* v_a_580_ = stack[5].m_obj;
lean_object* v_res_627_;
v_res_627_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
stack->m_obj
 = v_res_627_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___boxed(lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
lean_dec(v_a_629_);
lean_dec_ref(v_a_628_);
return v_res_635_;
}
}
lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(lean_object* v_cfg_636_, lean_object* v_types_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___x_647_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_646_);
lean_dec_ref_known(v___x_645_, 1);
v___x_647_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v_a_646_, v_cfg_636_, v_types_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
return v___x_647_;
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec(v_types_637_);
lean_dec_ref(v_cfg_636_);
v_a_648_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_645_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_645_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_636_ = stack[0].m_obj;
lean_object* v_types_637_ = stack[1].m_obj;
lean_object* v_a_638_ = stack[2].m_obj;
lean_object* v_a_639_ = stack[3].m_obj;
lean_object* v_a_640_ = stack[4].m_obj;
lean_object* v_a_641_ = stack[5].m_obj;
lean_object* v_a_642_ = stack[6].m_obj;
lean_object* v_a_643_ = stack[7].m_obj;
lean_object* v_res_656_;
v_res_656_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(v_cfg_636_, v_types_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
stack->m_obj
 = v_res_656_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext___boxed(lean_object* v_cfg_657_, lean_object* v_types_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(v_cfg_657_, v_types_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorIdx___impl(lean_object* v_x_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = lean_obj_tag_nat(v_x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorIdx___impl___boxed(lean_object* v_x_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorIdx___impl(v_x_669_);
lean_dec(v_x_669_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim___redArg(lean_object* v_t_671_, lean_object* v_k_672_){
_start:
{
if (lean_obj_tag(v_t_671_) == 1)
{
lean_object* v_path_673_; lean_object* v___x_674_; 
v_path_673_ = lean_ctor_get(v_t_671_, 0);
lean_inc_ref(v_path_673_);
lean_dec_ref_known(v_t_671_, 1);
v___x_674_ = lean_apply_1(v_k_672_, v_path_673_);
return v___x_674_;
}
else
{
lean_dec(v_t_671_);
return v_k_672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim(lean_object* v_motive_675_, lean_object* v_ctorIdx_676_, lean_object* v_t_677_, lean_object* v_h_678_, lean_object* v_k_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim___redArg(v_t_677_, v_k_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim___boxed(lean_object* v_motive_681_, lean_object* v_ctorIdx_682_, lean_object* v_t_683_, lean_object* v_h_684_, lean_object* v_k_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim(v_motive_681_, v_ctorIdx_682_, v_t_683_, v_h_684_, v_k_685_);
lean_dec(v_ctorIdx_682_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_normalize_elim___redArg(lean_object* v_t_687_, lean_object* v_normalize_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim___redArg(v_t_687_, v_normalize_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_normalize_elim(lean_object* v_motive_690_, lean_object* v_t_691_, lean_object* v_h_692_, lean_object* v_normalize_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim___redArg(v_t_691_, v_normalize_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_check_elim___redArg(lean_object* v_t_695_, lean_object* v_check_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim___redArg(v_t_695_, v_check_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_check_elim(lean_object* v_motive_698_, lean_object* v_t_699_, lean_object* v_h_700_, lean_object* v_check_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim___redArg(v_t_699_, v_check_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_decide_elim___redArg(lean_object* v_t_703_, lean_object* v_decide_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim___redArg(v_t_703_, v_decide_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_decide_elim(lean_object* v_motive_706_, lean_object* v_t_707_, lean_object* v_h_708_, lean_object* v_decide_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceAction_ctorElim___redArg(v_t_707_, v_decide_709_);
return v___x_710_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0(lean_object* v_x_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v___x_722_; 
lean_inc(v___y_716_);
lean_inc_ref(v___y_715_);
lean_inc(v___y_714_);
lean_inc_ref(v___y_713_);
lean_inc(v___y_712_);
v___x_722_ = lean_apply_10(v_x_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, lean_box(0));
return v___x_722_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_711_ = stack[0].m_obj;
lean_object* v___y_712_ = stack[1].m_obj;
lean_object* v___y_713_ = stack[2].m_obj;
lean_object* v___y_714_ = stack[3].m_obj;
lean_object* v___y_715_ = stack[4].m_obj;
lean_object* v___y_716_ = stack[5].m_obj;
lean_object* v___y_717_ = stack[6].m_obj;
lean_object* v___y_718_ = stack[7].m_obj;
lean_object* v___y_719_ = stack[8].m_obj;
lean_object* v___y_720_ = stack[9].m_obj;
lean_object* v_res_723_;
v_res_723_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0(v_x_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
stack->m_obj
 = v_res_723_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0___boxed(lean_object* v_x_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0(v_x_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
return v_res_735_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(lean_object* v_mvarId_736_, lean_object* v_x_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v___f_748_; lean_object* v___x_749_; 
lean_inc(v___y_742_);
lean_inc_ref(v___y_741_);
lean_inc(v___y_740_);
lean_inc_ref(v___y_739_);
lean_inc(v___y_738_);
v___f_748_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_748_, 0, v_x_737_);
lean_closure_set(v___f_748_, 1, v___y_738_);
lean_closure_set(v___f_748_, 2, v___y_739_);
lean_closure_set(v___f_748_, 3, v___y_740_);
lean_closure_set(v___f_748_, 4, v___y_741_);
lean_closure_set(v___f_748_, 5, v___y_742_);
v___x_749_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_736_, v___f_748_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
if (lean_obj_tag(v___x_749_) == 0)
{
return v___x_749_;
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_736_ = stack[0].m_obj;
lean_object* v_x_737_ = stack[1].m_obj;
lean_object* v___y_738_ = stack[2].m_obj;
lean_object* v___y_739_ = stack[3].m_obj;
lean_object* v___y_740_ = stack[4].m_obj;
lean_object* v___y_741_ = stack[5].m_obj;
lean_object* v___y_742_ = stack[6].m_obj;
lean_object* v___y_743_ = stack[7].m_obj;
lean_object* v___y_744_ = stack[8].m_obj;
lean_object* v___y_745_ = stack[9].m_obj;
lean_object* v___y_746_ = stack[10].m_obj;
lean_object* v_res_758_;
v_res_758_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v_mvarId_736_, v_x_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
stack->m_obj
 = v_res_758_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___boxed(lean_object* v_mvarId_759_, lean_object* v_x_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v_mvarId_759_, v_x_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
return v_res_771_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1(lean_object* v_00_u03b1_772_, lean_object* v_mvarId_773_, lean_object* v_x_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v_mvarId_773_, v_x_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
return v___x_785_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_773_ = stack[1].m_obj;
lean_object* v_x_774_ = stack[2].m_obj;
lean_object* v___y_775_ = stack[3].m_obj;
lean_object* v___y_776_ = stack[4].m_obj;
lean_object* v___y_777_ = stack[5].m_obj;
lean_object* v___y_778_ = stack[6].m_obj;
lean_object* v___y_779_ = stack[7].m_obj;
lean_object* v___y_780_ = stack[8].m_obj;
lean_object* v___y_781_ = stack[9].m_obj;
lean_object* v___y_782_ = stack[10].m_obj;
lean_object* v___y_783_ = stack[11].m_obj;
lean_object* v_res_786_;
v_res_786_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1(lean_box(0), v_mvarId_773_, v_x_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
stack->m_obj
 = v_res_786_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___boxed(lean_object* v_00_u03b1_787_, lean_object* v_mvarId_788_, lean_object* v_x_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1(v_00_u03b1_787_, v_mvarId_788_, v_x_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
return v_res_800_;
}
}
lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(lean_object* v_e_801_){
_start:
{
if (lean_obj_tag(v_e_801_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_811_; 
v_a_803_ = lean_ctor_get(v_e_801_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v_e_801_);
if (v_isSharedCheck_811_ == 0)
{
v___x_805_ = v_e_801_;
v_isShared_806_ = v_isSharedCheck_811_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v_e_801_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_811_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_809_; 
v___x_807_ = lean_mk_io_user_error(v_a_803_);
if (v_isShared_806_ == 0)
{
lean_ctor_set_tag(v___x_805_, 1);
lean_ctor_set(v___x_805_, 0, v___x_807_);
v___x_809_ = v___x_805_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
v_a_812_ = lean_ctor_get(v_e_801_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v_e_801_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v_e_801_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v_e_801_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
lean_ctor_set_tag(v___x_814_, 0);
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_801_ = stack[0].m_obj;
lean_object* v_res_820_;
v_res_820_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v_e_801_);
stack->m_obj
 = v_res_820_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg___boxed(lean_object* v_e_821_, lean_object* v_a_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v_e_821_);
return v_res_823_;
}
}
lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2(lean_object* v_00_u03b1_824_, lean_object* v_e_825_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v_e_825_);
return v___x_827_;
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_825_ = stack[1].m_obj;
lean_object* v_res_828_;
v_res_828_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2(lean_box(0), v_e_825_);
stack->m_obj
 = v_res_828_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___boxed(lean_object* v_00_u03b1_829_, lean_object* v_e_830_, lean_object* v_a_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2(v_00_u03b1_829_, v_e_830_);
return v_res_832_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(lean_object* v_msg_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_ref_839_; lean_object* v___x_840_; lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_849_; 
v_ref_839_ = lean_ctor_get(v___y_836_, 2);
v___x_840_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v_msg_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
v_a_841_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_849_ == 0)
{
v___x_843_ = v___x_840_;
v_isShared_844_ = v_isSharedCheck_849_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_840_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_849_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v___x_847_; 
lean_inc(v_ref_839_);
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v_ref_839_);
lean_ctor_set(v___x_845_, 1, v_a_841_);
if (v_isShared_844_ == 0)
{
lean_ctor_set_tag(v___x_843_, 1);
lean_ctor_set(v___x_843_, 0, v___x_845_);
v___x_847_ = v___x_843_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_833_ = stack[0].m_obj;
lean_object* v___y_834_ = stack[1].m_obj;
lean_object* v___y_835_ = stack[2].m_obj;
lean_object* v___y_836_ = stack[3].m_obj;
lean_object* v___y_837_ = stack[4].m_obj;
lean_object* v_res_850_;
v_res_850_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(v_msg_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
stack->m_obj
 = v_res_850_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg___boxed(lean_object* v_msg_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(v_msg_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
return v_res_857_;
}
}
lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(lean_object* v_target_860_, lean_object* v_ctx_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_exprDef_872_; lean_object* v_certDef_873_; lean_object* v_reflectionDef_874_; lean_object* v_solver_875_; lean_object* v_lratPath_876_; lean_object* v_config_877_; lean_object* v_restrictedTypes_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_1038_; 
v_exprDef_872_ = lean_ctor_get(v_ctx_861_, 0);
v_certDef_873_ = lean_ctor_get(v_ctx_861_, 1);
v_reflectionDef_874_ = lean_ctor_get(v_ctx_861_, 2);
v_solver_875_ = lean_ctor_get(v_ctx_861_, 3);
v_lratPath_876_ = lean_ctor_get(v_ctx_861_, 4);
v_config_877_ = lean_ctor_get(v_ctx_861_, 5);
v_restrictedTypes_878_ = lean_ctor_get(v_ctx_861_, 6);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_ctx_861_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_880_ = v_ctx_861_;
v_isShared_881_ = v_isSharedCheck_1038_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_restrictedTypes_878_);
lean_inc(v_config_877_);
lean_inc(v_lratPath_876_);
lean_inc(v_solver_875_);
lean_inc(v_reflectionDef_874_);
lean_inc(v_certDef_873_);
lean_inc(v_exprDef_872_);
lean_dec(v_ctx_861_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_1038_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v_timeout_906_; uint8_t v_trimProofs_907_; uint8_t v_binaryProofs_908_; uint8_t v_acNf_909_; uint8_t v_andFlattening_910_; uint8_t v_embeddedConstraintSubst_911_; uint8_t v_structures_912_; uint8_t v_fixedInt_913_; uint8_t v_enums_914_; uint8_t v_graphviz_915_; lean_object* v_maxSteps_916_; uint8_t v_shortCircuit_917_; uint8_t v_solverMode_918_; uint8_t v_uf_919_; lean_object* v_cegarRounds_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_1037_; 
v_timeout_906_ = lean_ctor_get(v_config_877_, 0);
v_trimProofs_907_ = lean_ctor_get_uint8(v_config_877_, sizeof(void*)*3);
v_binaryProofs_908_ = lean_ctor_get_uint8(v_config_877_, sizeof(void*)*3 + 1);
v_acNf_909_ = lean_ctor_get_uint8(v_config_877_, sizeof(void*)*3 + 2);
v_andFlattening_910_ = lean_ctor_get_uint8(v_config_877_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_911_ = lean_ctor_get_uint8(v_config_877_, sizeof(void*)*3 + 4);
v_structures_912_ = lean_ctor_get_uint8(v_config_877_, sizeof(void*)*3 + 5);
v_fixedInt_913_ = lean_ctor_get_uint8(v_config_877_, sizeof(void*)*3 + 6);
v_enums_914_ = lean_ctor_get_uint8(v_config_877_, sizeof(void*)*3 + 7);
v_graphviz_915_ = lean_ctor_get_uint8(v_config_877_, sizeof(void*)*3 + 8);
v_maxSteps_916_ = lean_ctor_get(v_config_877_, 1);
v_shortCircuit_917_ = lean_ctor_get_uint8(v_config_877_, sizeof(void*)*3 + 9);
v_solverMode_918_ = lean_ctor_get_uint8(v_config_877_, sizeof(void*)*3 + 10);
v_uf_919_ = lean_ctor_get_uint8(v_config_877_, sizeof(void*)*3 + 11);
v_cegarRounds_920_ = lean_ctor_get(v_config_877_, 2);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_config_877_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_922_ = v_config_877_;
v_isShared_923_ = v_isSharedCheck_1037_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_cegarRounds_920_);
lean_inc(v_maxSteps_916_);
lean_inc(v_timeout_906_);
lean_dec(v_config_877_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_1037_;
goto v_resetjp_921_;
}
v___jp_882_:
{
lean_object* v___x_892_; 
v___x_892_ = l_System_FilePath_fileName(v_lratPath_876_);
if (lean_obj_tag(v___x_892_) == 1)
{
lean_object* v_val_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_903_; 
v_val_893_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_903_ == 0)
{
v___x_895_ = v___x_892_;
v_isShared_896_ = v_isSharedCheck_903_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_val_893_);
lean_dec(v___x_892_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_903_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_897_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__0));
if (v_isShared_896_ == 0)
{
v___x_899_ = v___x_895_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_val_893_);
v___x_899_ = v_reuseFailAlloc_902_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_897_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
return v___x_901_;
}
}
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; 
lean_dec(v___x_892_);
v___x_904_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5, &l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5);
v___x_905_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(v___x_904_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
return v___x_905_;
}
}
v_resetjp_921_:
{
lean_object* v___x_924_; uint8_t v___x_925_; lean_object* v___x_927_; 
v___x_924_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_860_);
v___x_925_ = 0;
if (v_isShared_923_ == 0)
{
v___x_927_ = v___x_922_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_timeout_906_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_maxSteps_916_);
lean_ctor_set(v_reuseFailAlloc_1036_, 2, v_cegarRounds_920_);
lean_ctor_set_uint8(v_reuseFailAlloc_1036_, sizeof(void*)*3 + 1, v_binaryProofs_908_);
lean_ctor_set_uint8(v_reuseFailAlloc_1036_, sizeof(void*)*3 + 2, v_acNf_909_);
lean_ctor_set_uint8(v_reuseFailAlloc_1036_, sizeof(void*)*3 + 3, v_andFlattening_910_);
lean_ctor_set_uint8(v_reuseFailAlloc_1036_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_911_);
lean_ctor_set_uint8(v_reuseFailAlloc_1036_, sizeof(void*)*3 + 5, v_structures_912_);
lean_ctor_set_uint8(v_reuseFailAlloc_1036_, sizeof(void*)*3 + 6, v_fixedInt_913_);
lean_ctor_set_uint8(v_reuseFailAlloc_1036_, sizeof(void*)*3 + 7, v_enums_914_);
lean_ctor_set_uint8(v_reuseFailAlloc_1036_, sizeof(void*)*3 + 8, v_graphviz_915_);
lean_ctor_set_uint8(v_reuseFailAlloc_1036_, sizeof(void*)*3 + 9, v_shortCircuit_917_);
lean_ctor_set_uint8(v_reuseFailAlloc_1036_, sizeof(void*)*3 + 10, v_solverMode_918_);
lean_ctor_set_uint8(v_reuseFailAlloc_1036_, sizeof(void*)*3 + 11, v_uf_919_);
v___x_927_ = v_reuseFailAlloc_1036_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_929_; 
lean_ctor_set_uint8(v___x_927_, sizeof(void*)*3, v___x_925_);
lean_inc_ref(v_lratPath_876_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 5, v___x_927_);
v___x_929_ = v___x_880_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_exprDef_872_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_certDef_873_);
lean_ctor_set(v_reuseFailAlloc_1035_, 2, v_reflectionDef_874_);
lean_ctor_set(v_reuseFailAlloc_1035_, 3, v_solver_875_);
lean_ctor_set(v_reuseFailAlloc_1035_, 4, v_lratPath_876_);
lean_ctor_set(v_reuseFailAlloc_1035_, 5, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_1035_, 6, v_restrictedTypes_878_);
v___x_929_ = v_reuseFailAlloc_1035_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed), 12, 2);
lean_closure_set(v___x_930_, 0, v_target_860_);
lean_closure_set(v___x_930_, 1, v___x_929_);
v___x_931_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v___x_924_, v___x_930_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_1026_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_934_ = v___x_931_;
v_isShared_935_ = v_isSharedCheck_1026_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_931_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_1026_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v_lratCert_936_; 
v_lratCert_936_ = lean_ctor_get(v_a_932_, 1);
lean_inc(v_lratCert_936_);
if (lean_obj_tag(v_lratCert_936_) == 0)
{
lean_object* v_lemmas_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_948_; 
lean_dec_ref(v_lratPath_876_);
v_lemmas_937_ = lean_ctor_get(v_a_932_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v_a_932_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v_a_932_, 1);
lean_dec(v_unused_949_);
v___x_939_ = v_a_932_;
v_isShared_940_ = v_isSharedCheck_948_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_lemmas_937_);
lean_dec(v_a_932_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_948_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_941_ = lean_box(0);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_941_);
v___x_943_ = v___x_939_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_lemmas_937_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v___x_941_);
v___x_943_ = v_reuseFailAlloc_947_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_945_; 
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_943_);
v___x_945_ = v___x_934_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
else
{
lean_object* v_lemmas_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_1024_; 
v_lemmas_950_ = lean_ctor_get(v_a_932_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_a_932_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; 
v_unused_1025_ = lean_ctor_get(v_a_932_, 1);
lean_dec(v_unused_1025_);
v___x_952_ = v_a_932_;
v_isShared_953_ = v_isSharedCheck_1024_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_lemmas_950_);
lean_dec(v_a_932_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_1024_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_1022_; 
v_isSharedCheck_1022_ = !lean_is_exclusive(v_lratCert_936_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; 
v_unused_1023_ = lean_ctor_get(v_lratCert_936_, 0);
lean_dec(v_unused_1023_);
v___x_955_ = v_lratCert_936_;
v_isShared_956_ = v_isSharedCheck_1022_;
goto v_resetjp_954_;
}
else
{
lean_dec(v_lratCert_936_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_1022_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v___x_957_ = lean_array_get_size(v_lemmas_950_);
v___x_958_ = lean_unsigned_to_nat(0u);
v___x_959_ = lean_nat_dec_eq(v___x_957_, v___x_958_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_962_; 
lean_del_object(v___x_955_);
lean_dec_ref(v_lratPath_876_);
v___x_960_ = lean_box(2);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v___x_960_);
v___x_962_ = v___x_952_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_lemmas_950_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v___x_960_);
v___x_962_ = v_reuseFailAlloc_966_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_964_; 
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_962_);
v___x_964_ = v___x_934_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
else
{
lean_dec_ref(v_lemmas_950_);
lean_del_object(v___x_934_);
if (v_trimProofs_907_ == 0)
{
lean_del_object(v___x_955_);
lean_del_object(v___x_952_);
v___y_883_ = v_a_862_;
v___y_884_ = v_a_863_;
v___y_885_ = v_a_864_;
v___y_886_ = v_a_865_;
v___y_887_ = v_a_866_;
v___y_888_ = v_a_867_;
v___y_889_ = v_a_868_;
v___y_890_ = v_a_869_;
v___y_891_ = v_a_870_;
goto v___jp_882_;
}
else
{
lean_object* v_ref_967_; lean_object* v___x_968_; 
v_ref_967_ = lean_ctor_get(v_a_869_, 2);
v___x_968_ = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(v_lratPath_876_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref_known(v___x_968_, 1);
v___x_970_ = l_Lean_Meta_Tactic_BVDecide_LRAT_trim(v_a_969_);
lean_dec(v_a_969_);
v___x_971_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v___x_970_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_973_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref_known(v___x_971_, 1);
v___x_973_ = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(v_lratPath_876_, v_a_972_, v_binaryProofs_908_);
lean_dec(v_a_972_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_dec_ref_known(v___x_973_, 1);
lean_del_object(v___x_955_);
lean_del_object(v___x_952_);
v___y_883_ = v_a_862_;
v___y_884_ = v_a_863_;
v___y_885_ = v_a_864_;
v___y_886_ = v_a_865_;
v___y_887_ = v_a_866_;
v___y_888_ = v_a_867_;
v___y_889_ = v_a_868_;
v___y_890_ = v_a_869_;
v___y_891_ = v_a_870_;
goto v___jp_882_;
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_989_; 
lean_dec_ref(v_lratPath_876_);
v_a_974_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_989_ == 0)
{
v___x_976_ = v___x_973_;
v_isShared_977_ = v_isSharedCheck_989_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_989_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_978_ = lean_io_error_to_string(v_a_974_);
if (v_isShared_956_ == 0)
{
lean_ctor_set_tag(v___x_955_, 3);
lean_ctor_set(v___x_955_, 0, v___x_978_);
v___x_980_ = v___x_955_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_978_);
v___x_980_ = v_reuseFailAlloc_988_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_981_ = l_Lean_MessageData_ofFormat(v___x_980_);
lean_inc(v_ref_967_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v___x_981_);
lean_ctor_set(v___x_952_, 0, v_ref_967_);
v___x_983_ = v___x_952_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_ref_967_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v___x_981_);
v___x_983_ = v_reuseFailAlloc_987_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_985_; 
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_983_);
v___x_985_ = v___x_976_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1005_; 
lean_dec_ref(v_lratPath_876_);
v_a_990_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_992_ = v___x_971_;
v_isShared_993_ = v_isSharedCheck_1005_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_971_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1005_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_994_ = lean_io_error_to_string(v_a_990_);
if (v_isShared_956_ == 0)
{
lean_ctor_set_tag(v___x_955_, 3);
lean_ctor_set(v___x_955_, 0, v___x_994_);
v___x_996_ = v___x_955_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_994_);
v___x_996_ = v_reuseFailAlloc_1004_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_997_ = l_Lean_MessageData_ofFormat(v___x_996_);
lean_inc(v_ref_967_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v___x_997_);
lean_ctor_set(v___x_952_, 0, v_ref_967_);
v___x_999_ = v___x_952_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_ref_967_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1003_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1001_; 
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_999_);
v___x_1001_ = v___x_992_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1021_; 
lean_dec_ref(v_lratPath_876_);
v_a_1006_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1008_ = v___x_968_;
v_isShared_1009_ = v_isSharedCheck_1021_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_968_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1021_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1010_ = lean_io_error_to_string(v_a_1006_);
if (v_isShared_956_ == 0)
{
lean_ctor_set_tag(v___x_955_, 3);
lean_ctor_set(v___x_955_, 0, v___x_1010_);
v___x_1012_ = v___x_955_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1013_ = l_Lean_MessageData_ofFormat(v___x_1012_);
lean_inc(v_ref_967_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v___x_1013_);
lean_ctor_set(v___x_952_, 0, v_ref_967_);
v___x_1015_ = v___x_952_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_ref_967_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1017_; 
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1015_);
v___x_1017_ = v___x_1008_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
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
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec_ref(v_lratPath_876_);
v_a_1027_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_931_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_931_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_0interp(lean_interpreter_value* stack)
{
lean_object* v_target_860_ = stack[0].m_obj;
lean_object* v_ctx_861_ = stack[1].m_obj;
lean_object* v_a_862_ = stack[2].m_obj;
lean_object* v_a_863_ = stack[3].m_obj;
lean_object* v_a_864_ = stack[4].m_obj;
lean_object* v_a_865_ = stack[5].m_obj;
lean_object* v_a_866_ = stack[6].m_obj;
lean_object* v_a_867_ = stack[7].m_obj;
lean_object* v_a_868_ = stack[8].m_obj;
lean_object* v_a_869_ = stack[9].m_obj;
lean_object* v_a_870_ = stack[10].m_obj;
lean_object* v_res_1039_;
v_res_1039_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(v_target_860_, v_ctx_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_);
stack->m_obj
 = v_res_1039_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___boxed(lean_object* v_target_1040_, lean_object* v_ctx_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(v_target_1040_, v_ctx_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
return v_res_1052_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0(lean_object* v_00_u03b1_1053_, lean_object* v_msg_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(v_msg_1054_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
return v___x_1065_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1054_ = stack[1].m_obj;
lean_object* v___y_1055_ = stack[2].m_obj;
lean_object* v___y_1056_ = stack[3].m_obj;
lean_object* v___y_1057_ = stack[4].m_obj;
lean_object* v___y_1058_ = stack[5].m_obj;
lean_object* v___y_1059_ = stack[6].m_obj;
lean_object* v___y_1060_ = stack[7].m_obj;
lean_object* v___y_1061_ = stack[8].m_obj;
lean_object* v___y_1062_ = stack[9].m_obj;
lean_object* v___y_1063_ = stack[10].m_obj;
lean_object* v_res_1066_;
v_res_1066_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0(lean_box(0), v_msg_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
stack->m_obj
 = v_res_1066_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___boxed(lean_object* v_00_u03b1_1067_, lean_object* v_msg_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0(v_00_u03b1_1067_, v_msg_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
return v_res_1079_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1080_ = lean_box(0);
v___x_1081_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set(v___x_1082_, 1, v___x_1080_);
return v___x_1082_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg(){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0);
v___x_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1086_;
v_res_1086_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
stack->m_obj
 = v_res_1086_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___boxed(lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v_res_1088_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0(lean_object* v_00_u03b1_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1099_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1090_ = stack[1].m_obj;
lean_object* v___y_1091_ = stack[2].m_obj;
lean_object* v___y_1092_ = stack[3].m_obj;
lean_object* v___y_1093_ = stack[4].m_obj;
lean_object* v___y_1094_ = stack[5].m_obj;
lean_object* v___y_1095_ = stack[6].m_obj;
lean_object* v___y_1096_ = stack[7].m_obj;
lean_object* v___y_1097_ = stack[8].m_obj;
lean_object* v_res_1100_;
v_res_1100_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0(lean_box(0), v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
stack->m_obj
 = v_res_1100_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___boxed(lean_object* v_00_u03b1_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0(v_00_u03b1_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
return v_res_1111_;
}
}
lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(lean_object* v_snd_1112_, lean_object* v_ref_1113_, lean_object* v_a_x3f_1114_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_io_remove_file(v_snd_1112_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_dec(v_ref_1113_);
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1116_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1116_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1136_; 
v_a_1125_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1127_ = v___x_1116_;
v_isShared_1128_ = v_isSharedCheck_1136_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1116_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1136_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1129_ = lean_io_error_to_string(v_a_1125_);
v___x_1130_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
v___x_1131_ = l_Lean_MessageData_ofFormat(v___x_1130_);
v___x_1132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1132_, 0, v_ref_1113_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1132_);
v___x_1134_ = v___x_1127_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
}
LEAN_EXPORT void l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_1112_ = stack[0].m_obj;
lean_object* v_ref_1113_ = stack[1].m_obj;
lean_object* v_a_x3f_1114_ = stack[2].m_obj;
lean_object* v_res_1137_;
v_res_1137_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_1112_, v_ref_1113_, v_a_x3f_1114_);
stack->m_obj
 = v_res_1137_;
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0___boxed(lean_object* v_snd_1138_, lean_object* v_ref_1139_, lean_object* v_a_x3f_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_1138_, v_ref_1139_, v_a_x3f_1140_);
lean_dec(v_a_x3f_1140_);
lean_dec_ref(v_snd_1138_);
return v_res_1142_;
}
}
lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(lean_object* v_f_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_ref_1153_; lean_object* v___x_1154_; 
v_ref_1153_ = lean_ctor_get(v___y_1150_, 2);
v___x_1154_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v_fst_1156_; lean_object* v_snd_1157_; lean_object* v_r_1158_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___x_1154_, 1);
v_fst_1156_ = lean_ctor_get(v_a_1155_, 0);
lean_inc(v_fst_1156_);
v_snd_1157_ = lean_ctor_get(v_a_1155_, 1);
lean_inc_n(v_snd_1157_, 2);
lean_dec(v_a_1155_);
lean_inc(v___y_1151_);
lean_inc_ref(v___y_1150_);
lean_inc(v___y_1149_);
lean_inc_ref(v___y_1148_);
lean_inc(v___y_1147_);
lean_inc_ref(v___y_1146_);
lean_inc(v___y_1145_);
lean_inc_ref(v___y_1144_);
v_r_1158_ = lean_apply_11(v_f_1143_, v_fst_1156_, v_snd_1157_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, lean_box(0));
if (lean_obj_tag(v_r_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1183_; 
v_a_1159_ = lean_ctor_get(v_r_1158_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_r_1158_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1161_ = v_r_1158_;
v_isShared_1162_ = v_isSharedCheck_1183_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v_r_1158_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1183_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
lean_inc(v_a_1159_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set_tag(v___x_1161_, 1);
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1165_; 
lean_inc(v_ref_1153_);
v___x_1165_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_1157_, v_ref_1153_, v___x_1164_);
lean_dec_ref(v___x_1164_);
lean_dec(v_snd_1157_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; 
v_unused_1173_ = lean_ctor_get(v___x_1165_, 0);
lean_dec(v_unused_1173_);
v___x_1167_ = v___x_1165_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_dec(v___x_1165_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v_a_1159_);
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1159_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
lean_dec(v_a_1159_);
v_a_1174_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1165_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1165_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v_a_1184_ = lean_ctor_get(v_r_1158_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v_r_1158_, 1);
v___x_1185_ = lean_box(0);
lean_inc(v_ref_1153_);
v___x_1186_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_1157_, v_ref_1153_, v___x_1185_);
lean_dec(v_snd_1157_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1193_ == 0)
{
lean_object* v_unused_1194_; 
v_unused_1194_ = lean_ctor_get(v___x_1186_, 0);
lean_dec(v_unused_1194_);
v___x_1188_ = v___x_1186_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_dec(v___x_1186_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set_tag(v___x_1188_, 1);
lean_ctor_set(v___x_1188_, 0, v_a_1184_);
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1184_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
lean_dec(v_a_1184_);
v_a_1195_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1186_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1186_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1214_; 
lean_dec_ref(v_f_1143_);
v_a_1203_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1205_ = v___x_1154_;
v_isShared_1206_ = v_isSharedCheck_1214_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1154_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1214_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1207_ = lean_io_error_to_string(v_a_1203_);
v___x_1208_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
v___x_1209_ = l_Lean_MessageData_ofFormat(v___x_1208_);
lean_inc(v_ref_1153_);
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v_ref_1153_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___x_1210_);
v___x_1212_ = v___x_1205_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
}
LEAN_EXPORT void l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1143_ = stack[0].m_obj;
lean_object* v___y_1144_ = stack[1].m_obj;
lean_object* v___y_1145_ = stack[2].m_obj;
lean_object* v___y_1146_ = stack[3].m_obj;
lean_object* v___y_1147_ = stack[4].m_obj;
lean_object* v___y_1148_ = stack[5].m_obj;
lean_object* v___y_1149_ = stack[6].m_obj;
lean_object* v___y_1150_ = stack[7].m_obj;
lean_object* v___y_1151_ = stack[8].m_obj;
lean_object* v_res_1215_;
v_res_1215_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(v_f_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
stack->m_obj
 = v_res_1215_;
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___boxed(lean_object* v_f_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(v_f_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
return v_res_1226_;
}
}
lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1(lean_object* v_00_u03b1_1227_, lean_object* v_f_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(v_f_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
return v___x_1238_;
}
}
LEAN_EXPORT void l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1228_ = stack[1].m_obj;
lean_object* v___y_1229_ = stack[2].m_obj;
lean_object* v___y_1230_ = stack[3].m_obj;
lean_object* v___y_1231_ = stack[4].m_obj;
lean_object* v___y_1232_ = stack[5].m_obj;
lean_object* v___y_1233_ = stack[6].m_obj;
lean_object* v___y_1234_ = stack[7].m_obj;
lean_object* v___y_1235_ = stack[8].m_obj;
lean_object* v___y_1236_ = stack[9].m_obj;
lean_object* v_res_1239_;
v_res_1239_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1(lean_box(0), v_f_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
stack->m_obj
 = v_res_1239_;
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___boxed(lean_object* v_00_u03b1_1240_, lean_object* v_f_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1(v_00_u03b1_1240_, v_f_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
return v_res_1251_;
}
}
lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0(uint8_t v___x_1252_, uint8_t v___x_1253_, lean_object* v___x_1254_, lean_object* v___x_1255_, lean_object* v_a_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1258_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref_known(v___x_1266_, 1);
v___x_1268_ = lean_unsigned_to_nat(9u);
v___x_1269_ = lean_unsigned_to_nat(5u);
v___x_1270_ = lean_unsigned_to_nat(8u);
v___x_1271_ = lean_unsigned_to_nat(1000u);
v___x_1272_ = lean_unsigned_to_nat(1024u);
v___x_1273_ = lean_unsigned_to_nat(10000u);
v___x_1274_ = lean_unsigned_to_nat(1048576u);
v___x_1275_ = lean_unsigned_to_nat(50u);
v___x_1276_ = lean_box(0);
v___x_1277_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_1277_, 0, v___x_1268_);
lean_ctor_set(v___x_1277_, 1, v___x_1269_);
lean_ctor_set(v___x_1277_, 2, v___x_1270_);
lean_ctor_set(v___x_1277_, 3, v___x_1270_);
lean_ctor_set(v___x_1277_, 4, v___x_1271_);
lean_ctor_set(v___x_1277_, 5, v___x_1271_);
lean_ctor_set(v___x_1277_, 6, v___x_1254_);
lean_ctor_set(v___x_1277_, 7, v___x_1272_);
lean_ctor_set(v___x_1277_, 8, v___x_1273_);
lean_ctor_set(v___x_1277_, 9, v___x_1271_);
lean_ctor_set(v___x_1277_, 10, v___x_1274_);
lean_ctor_set(v___x_1277_, 11, v___x_1255_);
lean_ctor_set(v___x_1277_, 12, v___x_1275_);
lean_ctor_set(v___x_1277_, 13, v___x_1276_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14, v___x_1252_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 1, v___x_1252_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 2, v___x_1252_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 3, v___x_1252_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 4, v___x_1252_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 5, v___x_1253_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 6, v___x_1253_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 7, v___x_1253_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 8, v___x_1252_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 9, v___x_1252_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 10, v___x_1253_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 11, v___x_1252_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 12, v___x_1253_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 13, v___x_1253_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 14, v___x_1253_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 15, v___x_1253_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 16, v___x_1253_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 17, v___x_1252_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 18, v___x_1253_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 19, v___x_1253_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 20, v___x_1253_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 21, v___x_1253_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 22, v___x_1253_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 23, v___x_1253_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 24, v___x_1253_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 25, v___x_1253_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 26, v___x_1253_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 27, v___x_1253_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 28, v___x_1253_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 29, v___x_1253_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 30, v___x_1252_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 31, v___x_1253_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 32, v___x_1253_);
v___x_1278_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_1277_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1278_, 1);
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v_a_1267_);
v___x_1281_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed), 12, 2);
lean_closure_set(v___x_1281_, 0, v___x_1280_);
lean_closure_set(v___x_1281_, 1, v_a_1256_);
v___x_1282_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___x_1281_, v_a_1279_, v___x_1276_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_dec_ref_known(v___x_1282_, 1);
v___x_1283_ = lean_box(0);
v___x_1284_ = lean_box(0);
v___x_1285_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1283_, v___y_1258_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; 
v_unused_1293_ = lean_ctor_get(v___x_1285_, 0);
lean_dec(v_unused_1293_);
v___x_1287_ = v___x_1285_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_dec(v___x_1285_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v___x_1284_);
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1284_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
else
{
return v___x_1285_;
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
v_a_1294_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1282_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1282_);
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
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1256_);
v_a_1302_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1278_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1278_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_dec_ref(v_a_1256_);
lean_dec(v___x_1255_);
lean_dec(v___x_1254_);
v_a_1310_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1266_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1266_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1252_ = stack[0].m_num;
uint8_t v___x_1253_ = stack[1].m_num;
lean_object* v___x_1254_ = stack[2].m_obj;
lean_object* v___x_1255_ = stack[3].m_obj;
lean_object* v_a_1256_ = stack[4].m_obj;
lean_object* v___y_1257_ = stack[5].m_obj;
lean_object* v___y_1258_ = stack[6].m_obj;
lean_object* v___y_1259_ = stack[7].m_obj;
lean_object* v___y_1260_ = stack[8].m_obj;
lean_object* v___y_1261_ = stack[9].m_obj;
lean_object* v___y_1262_ = stack[10].m_obj;
lean_object* v___y_1263_ = stack[11].m_obj;
lean_object* v___y_1264_ = stack[12].m_obj;
lean_object* v_res_1318_;
v_res_1318_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0(v___x_1252_, v___x_1253_, v___x_1254_, v___x_1255_, v_a_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
stack->m_obj
 = v_res_1318_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0___boxed(lean_object* v___x_1319_, lean_object* v___x_1320_, lean_object* v___x_1321_, lean_object* v___x_1322_, lean_object* v_a_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
uint8_t v___x_5792__boxed_1333_; uint8_t v___x_5793__boxed_1334_; lean_object* v_res_1335_; 
v___x_5792__boxed_1333_ = lean_unbox(v___x_1319_);
v___x_5793__boxed_1334_ = lean_unbox(v___x_1320_);
v_res_1335_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0(v___x_5792__boxed_1333_, v___x_5793__boxed_1334_, v___x_1321_, v___x_1322_, v_a_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
return v_res_1335_;
}
}
lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1(lean_object* v_a_1336_, lean_object* v_a_1337_, uint8_t v___x_1338_, uint8_t v___x_1339_, lean_object* v___x_1340_, lean_object* v___x_1341_, lean_object* v_x_1342_, lean_object* v_lratFile_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new(v_lratFile_1343_, v_a_1336_, v_a_1337_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___f_1357_; lean_object* v___x_1358_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_a_1354_);
lean_dec_ref_known(v___x_1353_, 1);
v___x_1355_ = lean_box(v___x_1338_);
v___x_1356_ = lean_box(v___x_1339_);
v___f_1357_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0___boxed), 14, 5);
lean_closure_set(v___f_1357_, 0, v___x_1355_);
lean_closure_set(v___f_1357_, 1, v___x_1356_);
lean_closure_set(v___f_1357_, 2, v___x_1340_);
lean_closure_set(v___f_1357_, 3, v___x_1341_);
lean_closure_set(v___f_1357_, 4, v_a_1354_);
v___x_1358_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1357_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
return v___x_1358_;
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_dec(v___x_1341_);
lean_dec(v___x_1340_);
v_a_1359_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1353_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1353_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1336_ = stack[0].m_obj;
lean_object* v_a_1337_ = stack[1].m_obj;
uint8_t v___x_1338_ = stack[2].m_num;
uint8_t v___x_1339_ = stack[3].m_num;
lean_object* v___x_1340_ = stack[4].m_obj;
lean_object* v___x_1341_ = stack[5].m_obj;
lean_object* v_x_1342_ = stack[6].m_obj;
lean_object* v_lratFile_1343_ = stack[7].m_obj;
lean_object* v___y_1344_ = stack[8].m_obj;
lean_object* v___y_1345_ = stack[9].m_obj;
lean_object* v___y_1346_ = stack[10].m_obj;
lean_object* v___y_1347_ = stack[11].m_obj;
lean_object* v___y_1348_ = stack[12].m_obj;
lean_object* v___y_1349_ = stack[13].m_obj;
lean_object* v___y_1350_ = stack[14].m_obj;
lean_object* v___y_1351_ = stack[15].m_obj;
lean_object* v_res_1367_;
v_res_1367_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1(v_a_1336_, v_a_1337_, v___x_1338_, v___x_1339_, v___x_1340_, v___x_1341_, v_x_1342_, v_lratFile_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
stack->m_obj
 = v_res_1367_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1___boxed(lean_object** _args){
lean_object* v_a_1368_ = _args[0];
lean_object* v_a_1369_ = _args[1];
lean_object* v___x_1370_ = _args[2];
lean_object* v___x_1371_ = _args[3];
lean_object* v___x_1372_ = _args[4];
lean_object* v___x_1373_ = _args[5];
lean_object* v_x_1374_ = _args[6];
lean_object* v_lratFile_1375_ = _args[7];
lean_object* v___y_1376_ = _args[8];
lean_object* v___y_1377_ = _args[9];
lean_object* v___y_1378_ = _args[10];
lean_object* v___y_1379_ = _args[11];
lean_object* v___y_1380_ = _args[12];
lean_object* v___y_1381_ = _args[13];
lean_object* v___y_1382_ = _args[14];
lean_object* v___y_1383_ = _args[15];
lean_object* v___y_1384_ = _args[16];
_start:
{
uint8_t v___x_6023__boxed_1385_; uint8_t v___x_6024__boxed_1386_; lean_object* v_res_1387_; 
v___x_6023__boxed_1385_ = lean_unbox(v___x_1370_);
v___x_6024__boxed_1386_ = lean_unbox(v___x_1371_);
v_res_1387_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1(v_a_1368_, v_a_1369_, v___x_6023__boxed_1385_, v___x_6024__boxed_1386_, v___x_1372_, v___x_1373_, v_x_1374_, v_lratFile_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v_x_1374_);
return v_res_1387_;
}
}
lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide(lean_object* v_x_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1418_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3));
lean_inc(v_x_1408_);
v___x_1419_ = l_Lean_Syntax_isOfKind(v_x_1408_, v___x_1418_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; 
lean_dec(v_x_1408_);
v___x_1420_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1420_;
}
else
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; lean_object* v_types_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; 
v___x_1421_ = lean_unsigned_to_nat(1u);
v___x_1422_ = l_Lean_Syntax_getArg(v_x_1408_, v___x_1421_);
v___x_1423_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_1422_);
v___x_1424_ = l_Lean_Syntax_isOfKind(v___x_1422_, v___x_1423_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1466_; 
lean_dec(v___x_1422_);
lean_dec(v_x_1408_);
v___x_1466_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1466_;
}
else
{
lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1467_ = lean_unsigned_to_nat(2u);
v___x_1468_ = l_Lean_Syntax_getArg(v_x_1408_, v___x_1467_);
lean_dec(v_x_1408_);
v___x_1469_ = l_Lean_Syntax_isNone(v___x_1468_);
if (v___x_1469_ == 0)
{
uint8_t v___x_1470_; 
lean_inc(v___x_1468_);
v___x_1470_ = l_Lean_Syntax_matchesNull(v___x_1468_, v___x_1421_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1471_; 
lean_dec(v___x_1468_);
lean_dec(v___x_1422_);
v___x_1471_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1471_;
}
else
{
lean_object* v___x_1472_; lean_object* v_types_1473_; 
v___x_1472_ = lean_unsigned_to_nat(0u);
v_types_1473_ = l_Lean_Syntax_getArg(v___x_1468_, v___x_1472_);
lean_dec(v___x_1468_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1476_; uint8_t v___x_1477_; 
v___x_1476_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_types_1473_);
v___x_1477_ = l_Lean_Syntax_isOfKind(v_types_1473_, v___x_1476_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; 
lean_dec(v_types_1473_);
lean_dec(v___x_1422_);
v___x_1478_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1478_;
}
else
{
goto v___jp_1474_;
}
}
else
{
goto v___jp_1474_;
}
v___jp_1474_:
{
lean_object* v___x_1475_; 
v___x_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1475_, 0, v_types_1473_);
v_types_1426_ = v___x_1475_;
v___y_1427_ = v_a_1409_;
v___y_1428_ = v_a_1410_;
v___y_1429_ = v_a_1411_;
v___y_1430_ = v_a_1412_;
v___y_1431_ = v_a_1413_;
v___y_1432_ = v_a_1414_;
v___y_1433_ = v_a_1415_;
v___y_1434_ = v_a_1416_;
goto v___jp_1425_;
}
}
}
else
{
lean_object* v___x_1479_; 
lean_dec(v___x_1468_);
v___x_1479_ = lean_box(0);
v_types_1426_ = v___x_1479_;
v___y_1427_ = v_a_1409_;
v___y_1428_ = v_a_1410_;
v___y_1429_ = v_a_1411_;
v___y_1430_ = v_a_1412_;
v___y_1431_ = v_a_1413_;
v___y_1432_ = v_a_1414_;
v___y_1433_ = v_a_1415_;
v___y_1434_ = v_a_1416_;
goto v___jp_1425_;
}
}
v___jp_1425_:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v___x_1436_; uint8_t v___x_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
lean_dec_ref_known(v___x_1435_, 1);
v___x_1436_ = lean_unsigned_to_nat(10u);
v___x_1437_ = 0;
v___x_1438_ = lean_unsigned_to_nat(100000u);
v___x_1439_ = 0;
v___x_1440_ = lean_unsigned_to_nat(64u);
v___x_1441_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v___x_1441_, 0, v___x_1436_);
lean_ctor_set(v___x_1441_, 1, v___x_1438_);
lean_ctor_set(v___x_1441_, 2, v___x_1440_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*3, v___x_1424_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*3 + 1, v___x_1424_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*3 + 2, v___x_1437_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*3 + 3, v___x_1424_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*3 + 4, v___x_1424_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*3 + 5, v___x_1424_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*3 + 6, v___x_1424_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*3 + 7, v___x_1424_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*3 + 8, v___x_1437_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*3 + 9, v___x_1437_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*3 + 10, v___x_1439_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*3 + 11, v___x_1437_);
v___x_1442_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_1422_, v___x_1441_, v___x_1424_, v___y_1427_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1444_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_a_1443_);
lean_dec_ref_known(v___x_1442_, 1);
v___x_1444_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_types_1426_, v_a_1443_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___f_1448_; lean_object* v___x_1449_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref_known(v___x_1444_, 1);
v___x_1446_ = lean_box(v___x_1437_);
v___x_1447_ = lean_box(v___x_1424_);
v___f_1448_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1___boxed), 17, 6);
lean_closure_set(v___f_1448_, 0, v_a_1443_);
lean_closure_set(v___f_1448_, 1, v_a_1445_);
lean_closure_set(v___f_1448_, 2, v___x_1446_);
lean_closure_set(v___f_1448_, 3, v___x_1447_);
lean_closure_set(v___f_1448_, 4, v___x_1438_);
lean_closure_set(v___f_1448_, 5, v___x_1436_);
v___x_1449_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(v___f_1448_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
return v___x_1449_;
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec(v_a_1443_);
v_a_1450_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1444_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1444_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec(v_types_1426_);
v_a_1458_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1442_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1442_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
else
{
lean_dec(v_types_1426_);
lean_dec(v___x_1422_);
return v___x_1435_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_evalBvDecide_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1408_ = stack[0].m_obj;
lean_object* v_a_1409_ = stack[1].m_obj;
lean_object* v_a_1410_ = stack[2].m_obj;
lean_object* v_a_1411_ = stack[3].m_obj;
lean_object* v_a_1412_ = stack[4].m_obj;
lean_object* v_a_1413_ = stack[5].m_obj;
lean_object* v_a_1414_ = stack[6].m_obj;
lean_object* v_a_1415_ = stack[7].m_obj;
lean_object* v_a_1416_ = stack[8].m_obj;
lean_object* v_res_1480_;
v_res_1480_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide(v_x_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_);
stack->m_obj
 = v_res_1480_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___boxed(lean_object* v_x_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide(v_x_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_);
lean_dec(v_a_1489_);
lean_dec_ref(v_a_1488_);
lean_dec(v_a_1487_);
lean_dec_ref(v_a_1486_);
lean_dec(v_a_1485_);
lean_dec_ref(v_a_1484_);
lean_dec(v_a_1483_);
lean_dec_ref(v_a_1482_);
return v_res_1491_;
}
}
lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1(){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1501_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1502_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3));
v___x_1503_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2));
v___x_1504_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___boxed), 10, 0);
v___x_1505_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1501_, v___x_1502_, v___x_1503_, v___x_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1506_;
v_res_1506_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1();
stack->m_obj
 = v_res_1506_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___boxed(lean_object* v_a_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1();
return v_res_1508_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l_Array_mkArray0___redArg();
return v___x_1514_;
}
}
lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0(uint8_t v___x_1516_, lean_object* v___x_1517_, lean_object* v___x_1518_, lean_object* v___x_1519_, lean_object* v_a_1520_, lean_object* v_final_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_ref_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v_ref_1527_ = lean_ctor_get(v___y_1524_, 2);
v___x_1528_ = l_Lean_SourceInfo_fromRef(v_ref_1527_, v___x_1516_);
v___x_1529_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__0));
lean_inc_ref(v___x_1519_);
lean_inc_ref(v___x_1518_);
lean_inc_ref(v___x_1517_);
v___x_1530_ = l_Lean_Name_mkStr4(v___x_1517_, v___x_1518_, v___x_1519_, v___x_1529_);
v___x_1531_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__1));
v___x_1532_ = l_Lean_Name_mkStr4(v___x_1517_, v___x_1518_, v___x_1519_, v___x_1531_);
v___x_1533_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3));
v___x_1534_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4);
v___x_1535_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5));
v___x_1536_ = lean_array_push(v_a_1520_, v_final_1521_);
v___x_1537_ = l_Lean_Syntax_SepArray_ofElems(v___x_1535_, v___x_1536_);
lean_dec_ref(v___x_1536_);
v___x_1538_ = l_Array_append___redArg(v___x_1534_, v___x_1537_);
lean_dec_ref(v___x_1537_);
lean_inc_n(v___x_1528_, 2);
v___x_1539_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1528_);
lean_ctor_set(v___x_1539_, 1, v___x_1533_);
lean_ctor_set(v___x_1539_, 2, v___x_1538_);
v___x_1540_ = l_Lean_Syntax_node1(v___x_1528_, v___x_1532_, v___x_1539_);
v___x_1541_ = l_Lean_Syntax_node1(v___x_1528_, v___x_1530_, v___x_1540_);
v___x_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1516_ = stack[0].m_num;
lean_object* v___x_1517_ = stack[1].m_obj;
lean_object* v___x_1518_ = stack[2].m_obj;
lean_object* v___x_1519_ = stack[3].m_obj;
lean_object* v_a_1520_ = stack[4].m_obj;
lean_object* v_final_1521_ = stack[5].m_obj;
lean_object* v___y_1522_ = stack[6].m_obj;
lean_object* v___y_1523_ = stack[7].m_obj;
lean_object* v___y_1524_ = stack[8].m_obj;
lean_object* v___y_1525_ = stack[9].m_obj;
lean_object* v_res_1543_;
v_res_1543_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0(v___x_1516_, v___x_1517_, v___x_1518_, v___x_1519_, v_a_1520_, v_final_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
stack->m_obj
 = v_res_1543_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___boxed(lean_object* v___x_1544_, lean_object* v___x_1545_, lean_object* v___x_1546_, lean_object* v___x_1547_, lean_object* v_a_1548_, lean_object* v_final_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
uint8_t v___x_54120__boxed_1555_; lean_object* v_res_1556_; 
v___x_54120__boxed_1555_ = lean_unbox(v___x_1544_);
v_res_1556_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0(v___x_54120__boxed_1555_, v___x_1545_, v___x_1546_, v___x_1547_, v_a_1548_, v_final_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
return v_res_1556_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__14(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5));
v___x_1593_ = l_String_toRawSubstring_x27(v___x_1592_);
return v___x_1593_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg(size_t v_sz_1650_, size_t v_i_1651_, lean_object* v_bs_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
uint8_t v___x_1658_; 
v___x_1658_ = lean_usize_dec_lt(v_i_1651_, v_sz_1650_);
if (v___x_1658_ == 0)
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v_bs_1652_);
return v___x_1659_;
}
else
{
lean_object* v_v_1660_; lean_object* v_hyp_1661_; lean_object* v_tacticProof_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1747_; 
v_v_1660_ = lean_array_uget(v_bs_1652_, v_i_1651_);
v_hyp_1661_ = lean_ctor_get(v_v_1660_, 0);
v_tacticProof_1662_ = lean_ctor_get(v_v_1660_, 1);
v_isSharedCheck_1747_ = !lean_is_exclusive(v_v_1660_);
if (v_isSharedCheck_1747_ == 0)
{
lean_object* v_unused_1748_; 
v_unused_1748_ = lean_ctor_get(v_v_1660_, 2);
lean_dec(v_unused_1748_);
v___x_1664_ = v_v_1660_;
v_isShared_1665_ = v_isSharedCheck_1747_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_tacticProof_1662_);
lean_inc(v_hyp_1661_);
lean_dec(v_v_1660_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1747_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v_type_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1743_; 
v_type_1666_ = lean_ctor_get(v_hyp_1661_, 1);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_hyp_1661_);
if (v_isSharedCheck_1743_ == 0)
{
lean_object* v_unused_1744_; lean_object* v_unused_1745_; lean_object* v_unused_1746_; 
v_unused_1744_ = lean_ctor_get(v_hyp_1661_, 3);
lean_dec(v_unused_1744_);
v_unused_1745_ = lean_ctor_get(v_hyp_1661_, 2);
lean_dec(v_unused_1745_);
v_unused_1746_ = lean_ctor_get(v_hyp_1661_, 0);
lean_dec(v_unused_1746_);
v___x_1668_ = v_hyp_1661_;
v_isShared_1669_ = v_isSharedCheck_1743_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_type_1666_);
lean_dec(v_hyp_1661_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1743_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1670_; lean_object* v_bs_x27_1671_; lean_object* v_a_1673_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1670_ = lean_unsigned_to_nat(0u);
v_bs_x27_1671_ = lean_array_uset(v_bs_1652_, v_i_1651_, v___x_1670_);
v___x_1678_ = lean_box(1);
v___x_1679_ = l_Lean_PrettyPrinter_delab(v_type_1666_, v___x_1678_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1681_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1680_);
lean_dec_ref_known(v___x_1679_, 1);
lean_inc(v___y_1656_);
lean_inc_ref(v___y_1655_);
lean_inc(v___y_1654_);
lean_inc_ref(v___y_1653_);
v___x_1681_ = lean_apply_5(v_tacticProof_1662_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, lean_box(0));
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_toCold_1682_; lean_object* v_a_1683_; lean_object* v_ref_1684_; lean_object* v_quotContext_1685_; lean_object* v_currMacroScope_1686_; uint8_t v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1696_; 
v_toCold_1682_ = lean_ctor_get(v___y_1655_, 0);
v_a_1683_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1683_);
lean_dec_ref_known(v___x_1681_, 1);
v_ref_1684_ = lean_ctor_get(v___y_1655_, 2);
v_quotContext_1685_ = lean_ctor_get(v_toCold_1682_, 8);
v_currMacroScope_1686_ = lean_ctor_get(v_toCold_1682_, 9);
v___x_1687_ = 0;
v___x_1688_ = l_Lean_SourceInfo_fromRef(v_ref_1684_, v___x_1687_);
v___x_1689_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__1));
v___x_1690_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__2));
lean_inc_n(v___x_1688_, 2);
v___x_1691_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1688_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__5));
v___x_1693_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3));
v___x_1694_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4);
if (v_isShared_1665_ == 0)
{
lean_ctor_set_tag(v___x_1664_, 1);
lean_ctor_set(v___x_1664_, 2, v___x_1694_);
lean_ctor_set(v___x_1664_, 1, v___x_1693_);
lean_ctor_set(v___x_1664_, 0, v___x_1688_);
v___x_1696_ = v___x_1664_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1688_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v___x_1693_);
lean_ctor_set(v_reuseFailAlloc_1725_, 2, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1707_; 
lean_inc_ref(v___x_1696_);
lean_inc_n(v___x_1688_, 2);
v___x_1697_ = l_Lean_Syntax_node1(v___x_1688_, v___x_1692_, v___x_1696_);
v___x_1698_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__7));
v___x_1699_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__9));
v___x_1700_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__11));
v___x_1701_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__13));
v___x_1702_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__14);
v___x_1703_ = lean_box(0);
lean_inc(v_currMacroScope_1686_);
lean_inc(v_quotContext_1685_);
v___x_1704_ = l_Lean_addMacroScope(v_quotContext_1685_, v___x_1703_, v_currMacroScope_1686_);
v___x_1705_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__28));
if (v_isShared_1669_ == 0)
{
lean_ctor_set_tag(v___x_1668_, 3);
lean_ctor_set(v___x_1668_, 3, v___x_1705_);
lean_ctor_set(v___x_1668_, 2, v___x_1704_);
lean_ctor_set(v___x_1668_, 1, v___x_1702_);
lean_ctor_set(v___x_1668_, 0, v___x_1688_);
v___x_1707_ = v___x_1668_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1688_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v___x_1702_);
lean_ctor_set(v_reuseFailAlloc_1724_, 2, v___x_1704_);
lean_ctor_set(v_reuseFailAlloc_1724_, 3, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
lean_inc_n(v___x_1688_, 10);
v___x_1708_ = l_Lean_Syntax_node1(v___x_1688_, v___x_1701_, v___x_1707_);
v___x_1709_ = l_Lean_Syntax_node1(v___x_1688_, v___x_1700_, v___x_1708_);
v___x_1710_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__30));
v___x_1711_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__31));
v___x_1712_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1688_);
lean_ctor_set(v___x_1712_, 1, v___x_1711_);
v___x_1713_ = l_Lean_Syntax_node2(v___x_1688_, v___x_1710_, v___x_1712_, v_a_1680_);
v___x_1714_ = l_Lean_Syntax_node1(v___x_1688_, v___x_1693_, v___x_1713_);
v___x_1715_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__32));
v___x_1716_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1688_);
lean_ctor_set(v___x_1716_, 1, v___x_1715_);
v___x_1717_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__34));
v___x_1718_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___closed__35));
v___x_1719_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1688_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
v___x_1720_ = l_Lean_Syntax_node2(v___x_1688_, v___x_1717_, v___x_1719_, v_a_1683_);
v___x_1721_ = l_Lean_Syntax_node5(v___x_1688_, v___x_1699_, v___x_1709_, v___x_1696_, v___x_1714_, v___x_1716_, v___x_1720_);
v___x_1722_ = l_Lean_Syntax_node1(v___x_1688_, v___x_1698_, v___x_1721_);
v___x_1723_ = l_Lean_Syntax_node3(v___x_1688_, v___x_1689_, v___x_1691_, v___x_1697_, v___x_1722_);
v_a_1673_ = v___x_1723_;
goto v___jp_1672_;
}
}
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_dec(v_a_1680_);
lean_dec_ref(v_bs_x27_1671_);
lean_del_object(v___x_1668_);
lean_del_object(v___x_1664_);
v_a_1726_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1681_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1681_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
else
{
lean_del_object(v___x_1668_);
lean_del_object(v___x_1664_);
lean_dec_ref(v_tacticProof_1662_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1734_; 
v_a_1734_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1734_);
lean_dec_ref_known(v___x_1679_, 1);
v_a_1673_ = v_a_1734_;
goto v___jp_1672_;
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_dec_ref(v_bs_x27_1671_);
v_a_1735_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1679_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1679_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
v___jp_1672_:
{
size_t v___x_1674_; size_t v___x_1675_; lean_object* v___x_1676_; 
v___x_1674_ = ((size_t)1ULL);
v___x_1675_ = lean_usize_add(v_i_1651_, v___x_1674_);
v___x_1676_ = lean_array_uset(v_bs_x27_1671_, v_i_1651_, v_a_1673_);
v_i_1651_ = v___x_1675_;
v_bs_1652_ = v___x_1676_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1650_ = stack[0].m_num;
size_t v_i_1651_ = stack[1].m_num;
lean_object* v_bs_1652_ = stack[2].m_obj;
lean_object* v___y_1653_ = stack[3].m_obj;
lean_object* v___y_1654_ = stack[4].m_obj;
lean_object* v___y_1655_ = stack[5].m_obj;
lean_object* v___y_1656_ = stack[6].m_obj;
lean_object* v_res_1749_;
v_res_1749_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg(v_sz_1650_, v_i_1651_, v_bs_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
stack->m_obj
 = v_res_1749_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg___boxed(lean_object* v_sz_1750_, lean_object* v_i_1751_, lean_object* v_bs_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
size_t v_sz_boxed_1758_; size_t v_i_boxed_1759_; lean_object* v_res_1760_; 
v_sz_boxed_1758_ = lean_unbox_usize(v_sz_1750_);
lean_dec(v_sz_1750_);
v_i_boxed_1759_ = lean_unbox_usize(v_i_1751_);
lean_dec(v_i_1751_);
v_res_1760_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg(v_sz_boxed_1758_, v_i_boxed_1759_, v_bs_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
return v_res_1760_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0(size_t v_sz_1761_, size_t v_i_1762_, lean_object* v_bs_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___redArg(v_sz_1761_, v_i_1762_, v_bs_1763_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
return v___x_1774_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1761_ = stack[0].m_num;
size_t v_i_1762_ = stack[1].m_num;
lean_object* v_bs_1763_ = stack[2].m_obj;
lean_object* v___y_1764_ = stack[3].m_obj;
lean_object* v___y_1765_ = stack[4].m_obj;
lean_object* v___y_1766_ = stack[5].m_obj;
lean_object* v___y_1767_ = stack[6].m_obj;
lean_object* v___y_1768_ = stack[7].m_obj;
lean_object* v___y_1769_ = stack[8].m_obj;
lean_object* v___y_1770_ = stack[9].m_obj;
lean_object* v___y_1771_ = stack[10].m_obj;
lean_object* v___y_1772_ = stack[11].m_obj;
lean_object* v_res_1775_;
v_res_1775_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0(v_sz_1761_, v_i_1762_, v_bs_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
stack->m_obj
 = v_res_1775_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___boxed(lean_object* v_sz_1776_, lean_object* v_i_1777_, lean_object* v_bs_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
size_t v_sz_boxed_1789_; size_t v_i_boxed_1790_; lean_object* v_res_1791_; 
v_sz_boxed_1789_ = lean_unbox_usize(v_sz_1776_);
lean_dec(v_sz_1776_);
v_i_boxed_1790_ = lean_unbox_usize(v_i_1777_);
lean_dec(v_i_1777_);
v_res_1791_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0(v_sz_boxed_1789_, v_i_boxed_1790_, v_bs_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
return v_res_1791_;
}
}
lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1(lean_object* v___x_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, uint8_t v___x_1803_, lean_object* v___x_1804_, lean_object* v___x_1805_, lean_object* v___x_1806_, lean_object* v___x_1807_, lean_object* v_tk_1808_, lean_object* v_typesStx_1809_, lean_object* v___x_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(v___x_1800_, v_a_1801_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v_lemmas_1823_; lean_object* v_action_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1955_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1822_);
lean_dec_ref_known(v___x_1821_, 1);
v_lemmas_1823_ = lean_ctor_get(v_a_1822_, 0);
v_action_1824_ = lean_ctor_get(v_a_1822_, 1);
v_isSharedCheck_1955_ = !lean_is_exclusive(v_a_1822_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1826_ = v_a_1822_;
v_isShared_1827_ = v_isSharedCheck_1955_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_action_1824_);
lean_inc(v_lemmas_1823_);
lean_dec(v_a_1822_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1955_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
size_t v_sz_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v_sz_1828_ = lean_array_size(v_lemmas_1823_);
v___x_1829_ = lean_box_usize(v_sz_1828_);
v___x_1830_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___boxed__const__1));
v___x_1831_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_spec__0___boxed), 13, 3);
lean_closure_set(v___x_1831_, 0, v___x_1829_);
lean_closure_set(v___x_1831_, 1, v___x_1830_);
lean_closure_set(v___x_1831_, 2, v_lemmas_1823_);
v___x_1832_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v_a_1802_, v___x_1831_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1832_) == 0)
{
switch(lean_obj_tag(v_action_1824_))
{
case 0:
{
lean_object* v_a_1833_; lean_object* v_ref_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_a_1833_);
lean_dec_ref_known(v___x_1832_, 1);
v_ref_1834_ = lean_ctor_get(v___y_1818_, 2);
v___x_1835_ = l_Lean_SourceInfo_fromRef(v_ref_1834_, v___x_1803_);
v___x_1836_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__0));
lean_inc_ref(v___x_1806_);
lean_inc_ref(v___x_1805_);
lean_inc_ref(v___x_1804_);
v___x_1837_ = l_Lean_Name_mkStr4(v___x_1804_, v___x_1805_, v___x_1806_, v___x_1836_);
v___x_1838_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__1));
lean_inc(v___x_1835_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set_tag(v___x_1826_, 2);
lean_ctor_set(v___x_1826_, 1, v___x_1838_);
lean_ctor_set(v___x_1826_, 0, v___x_1835_);
v___x_1840_ = v___x_1826_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1835_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___y_1844_; 
v___x_1841_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3));
v___x_1842_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4);
if (lean_obj_tag(v_typesStx_1809_) == 1)
{
lean_object* v_val_1866_; lean_object* v___x_1867_; 
v_val_1866_ = lean_ctor_get(v_typesStx_1809_, 0);
lean_inc(v_val_1866_);
lean_dec_ref_known(v_typesStx_1809_, 1);
v___x_1867_ = l_Array_mkArray1___redArg(v_val_1866_);
v___y_1844_ = v___x_1867_;
goto v___jp_1843_;
}
else
{
lean_object* v___x_1868_; 
lean_dec(v_typesStx_1809_);
v___x_1868_ = lean_mk_empty_array_with_capacity(v___x_1810_);
v___y_1844_ = v___x_1868_;
goto v___jp_1843_;
}
v___jp_1843_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1865_; 
v___x_1845_ = l_Array_append___redArg(v___x_1842_, v___y_1844_);
lean_dec_ref(v___y_1844_);
lean_inc(v___x_1835_);
v___x_1846_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1835_);
lean_ctor_set(v___x_1846_, 1, v___x_1841_);
lean_ctor_set(v___x_1846_, 2, v___x_1845_);
v___x_1847_ = l_Lean_Syntax_node3(v___x_1835_, v___x_1837_, v___x_1840_, v___x_1807_, v___x_1846_);
lean_inc_ref(v___x_1806_);
lean_inc_ref(v___x_1805_);
lean_inc_ref(v___x_1804_);
v___x_1848_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0(v___x_1803_, v___x_1804_, v___x_1805_, v___x_1806_, v_a_1833_, v___x_1847_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1851_ = v___x_1848_;
v_isShared_1852_ = v_isSharedCheck_1865_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1848_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1865_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1859_; 
v___x_1853_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__0));
v___x_1854_ = l_Lean_Name_mkStr4(v___x_1804_, v___x_1805_, v___x_1806_, v___x_1853_);
v___x_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
lean_ctor_set(v___x_1855_, 1, v_a_1849_);
v___x_1856_ = lean_box(0);
v___x_1857_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1855_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
lean_ctor_set(v___x_1857_, 2, v___x_1856_);
lean_ctor_set(v___x_1857_, 3, v___x_1856_);
lean_ctor_set(v___x_1857_, 4, v___x_1856_);
lean_ctor_set(v___x_1857_, 5, v___x_1856_);
lean_inc(v_ref_1834_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set_tag(v___x_1851_, 1);
lean_ctor_set(v___x_1851_, 0, v_ref_1834_);
v___x_1859_ = v___x_1851_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_ref_1834_);
v___x_1859_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v___x_1860_; uint8_t v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1860_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__2));
v___x_1861_ = 4;
v___x_1862_ = l_Lean_MessageData_nil;
v___x_1863_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1808_, v___x_1857_, v___x_1859_, v___x_1860_, v___x_1856_, v___x_1861_, v___x_1862_, v___y_1818_, v___y_1819_);
return v___x_1863_;
}
}
}
}
}
case 1:
{
lean_object* v_a_1870_; lean_object* v_path_1871_; lean_object* v_ref_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1878_; 
v_a_1870_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_a_1870_);
lean_dec_ref_known(v___x_1832_, 1);
v_path_1871_ = lean_ctor_get(v_action_1824_, 0);
lean_inc_ref(v_path_1871_);
lean_dec_ref_known(v_action_1824_, 1);
v_ref_1872_ = lean_ctor_get(v___y_1818_, 2);
v___x_1873_ = l_Lean_SourceInfo_fromRef(v_ref_1872_, v___x_1803_);
v___x_1874_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__3));
lean_inc_ref(v___x_1806_);
lean_inc_ref(v___x_1805_);
lean_inc_ref(v___x_1804_);
v___x_1875_ = l_Lean_Name_mkStr4(v___x_1804_, v___x_1805_, v___x_1806_, v___x_1874_);
v___x_1876_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__4));
lean_inc(v___x_1873_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set_tag(v___x_1826_, 2);
lean_ctor_set(v___x_1826_, 1, v___x_1876_);
lean_ctor_set(v___x_1826_, 0, v___x_1873_);
v___x_1878_ = v___x_1826_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1873_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___y_1882_; 
v___x_1879_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3));
v___x_1880_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4);
if (lean_obj_tag(v_typesStx_1809_) == 1)
{
lean_object* v_val_1906_; lean_object* v___x_1907_; 
v_val_1906_ = lean_ctor_get(v_typesStx_1809_, 0);
lean_inc(v_val_1906_);
lean_dec_ref_known(v_typesStx_1809_, 1);
v___x_1907_ = l_Array_mkArray1___redArg(v_val_1906_);
v___y_1882_ = v___x_1907_;
goto v___jp_1881_;
}
else
{
lean_object* v___x_1908_; 
lean_dec(v_typesStx_1809_);
v___x_1908_ = lean_mk_empty_array_with_capacity(v___x_1810_);
v___y_1882_ = v___x_1908_;
goto v___jp_1881_;
}
v___jp_1881_:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1905_; 
v___x_1883_ = l_Array_append___redArg(v___x_1880_, v___y_1882_);
lean_dec_ref(v___y_1882_);
lean_inc(v___x_1873_);
v___x_1884_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1873_);
lean_ctor_set(v___x_1884_, 1, v___x_1879_);
lean_ctor_set(v___x_1884_, 2, v___x_1883_);
v___x_1885_ = lean_box(2);
v___x_1886_ = l_Lean_Syntax_mkStrLit(v_path_1871_, v___x_1885_);
v___x_1887_ = l_Lean_Syntax_node4(v___x_1873_, v___x_1875_, v___x_1878_, v___x_1807_, v___x_1884_, v___x_1886_);
lean_inc_ref(v___x_1806_);
lean_inc_ref(v___x_1805_);
lean_inc_ref(v___x_1804_);
v___x_1888_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0(v___x_1803_, v___x_1804_, v___x_1805_, v___x_1806_, v_a_1870_, v___x_1887_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1891_ = v___x_1888_;
v_isShared_1892_ = v_isSharedCheck_1905_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1905_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1899_; 
v___x_1893_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__0));
v___x_1894_ = l_Lean_Name_mkStr4(v___x_1804_, v___x_1805_, v___x_1806_, v___x_1893_);
v___x_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
lean_ctor_set(v___x_1895_, 1, v_a_1889_);
v___x_1896_ = lean_box(0);
v___x_1897_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1895_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
lean_ctor_set(v___x_1897_, 2, v___x_1896_);
lean_ctor_set(v___x_1897_, 3, v___x_1896_);
lean_ctor_set(v___x_1897_, 4, v___x_1896_);
lean_ctor_set(v___x_1897_, 5, v___x_1896_);
lean_inc(v_ref_1872_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set_tag(v___x_1891_, 1);
lean_ctor_set(v___x_1891_, 0, v_ref_1872_);
v___x_1899_ = v___x_1891_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_ref_1872_);
v___x_1899_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
lean_object* v___x_1900_; uint8_t v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1900_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__2));
v___x_1901_ = 4;
v___x_1902_ = l_Lean_MessageData_nil;
v___x_1903_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1808_, v___x_1897_, v___x_1899_, v___x_1900_, v___x_1896_, v___x_1901_, v___x_1902_, v___y_1818_, v___y_1819_);
return v___x_1903_;
}
}
}
}
}
default: 
{
lean_object* v_a_1910_; lean_object* v_ref_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1917_; 
v_a_1910_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v___x_1832_, 1);
v_ref_1911_ = lean_ctor_get(v___y_1818_, 2);
v___x_1912_ = l_Lean_SourceInfo_fromRef(v_ref_1911_, v___x_1803_);
v___x_1913_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__2));
lean_inc_ref(v___x_1806_);
lean_inc_ref(v___x_1805_);
lean_inc_ref(v___x_1804_);
v___x_1914_ = l_Lean_Name_mkStr4(v___x_1804_, v___x_1805_, v___x_1806_, v___x_1913_);
v___x_1915_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__5));
lean_inc(v___x_1912_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set_tag(v___x_1826_, 2);
lean_ctor_set(v___x_1826_, 1, v___x_1915_);
lean_ctor_set(v___x_1826_, 0, v___x_1912_);
v___x_1917_ = v___x_1826_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1912_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v___x_1915_);
v___x_1917_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___y_1921_; 
v___x_1918_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3));
v___x_1919_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4);
if (lean_obj_tag(v_typesStx_1809_) == 1)
{
lean_object* v_val_1943_; lean_object* v___x_1944_; 
v_val_1943_ = lean_ctor_get(v_typesStx_1809_, 0);
lean_inc(v_val_1943_);
lean_dec_ref_known(v_typesStx_1809_, 1);
v___x_1944_ = l_Array_mkArray1___redArg(v_val_1943_);
v___y_1921_ = v___x_1944_;
goto v___jp_1920_;
}
else
{
lean_object* v___x_1945_; 
lean_dec(v_typesStx_1809_);
v___x_1945_ = lean_mk_empty_array_with_capacity(v___x_1810_);
v___y_1921_ = v___x_1945_;
goto v___jp_1920_;
}
v___jp_1920_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1942_; 
v___x_1922_ = l_Array_append___redArg(v___x_1919_, v___y_1921_);
lean_dec_ref(v___y_1921_);
lean_inc(v___x_1912_);
v___x_1923_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1912_);
lean_ctor_set(v___x_1923_, 1, v___x_1918_);
lean_ctor_set(v___x_1923_, 2, v___x_1922_);
v___x_1924_ = l_Lean_Syntax_node3(v___x_1912_, v___x_1914_, v___x_1917_, v___x_1807_, v___x_1923_);
lean_inc_ref(v___x_1806_);
lean_inc_ref(v___x_1805_);
lean_inc_ref(v___x_1804_);
v___x_1925_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0(v___x_1803_, v___x_1804_, v___x_1805_, v___x_1806_, v_a_1910_, v___x_1924_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1942_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1942_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1930_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__0));
v___x_1931_ = l_Lean_Name_mkStr4(v___x_1804_, v___x_1805_, v___x_1806_, v___x_1930_);
v___x_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
lean_ctor_set(v___x_1932_, 1, v_a_1926_);
v___x_1933_ = lean_box(0);
v___x_1934_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1932_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
lean_ctor_set(v___x_1934_, 2, v___x_1933_);
lean_ctor_set(v___x_1934_, 3, v___x_1933_);
lean_ctor_set(v___x_1934_, 4, v___x_1933_);
lean_ctor_set(v___x_1934_, 5, v___x_1933_);
lean_inc(v_ref_1911_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set_tag(v___x_1928_, 1);
lean_ctor_set(v___x_1928_, 0, v_ref_1911_);
v___x_1936_ = v___x_1928_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_ref_1911_);
v___x_1936_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1937_; uint8_t v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1937_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__2));
v___x_1938_ = 4;
v___x_1939_ = l_Lean_MessageData_nil;
v___x_1940_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1808_, v___x_1934_, v___x_1936_, v___x_1937_, v___x_1933_, v___x_1938_, v___x_1939_, v___y_1818_, v___y_1819_);
return v___x_1940_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_del_object(v___x_1826_);
lean_dec(v_action_1824_);
lean_dec(v_typesStx_1809_);
lean_dec(v_tk_1808_);
lean_dec(v___x_1807_);
lean_dec_ref(v___x_1806_);
lean_dec_ref(v___x_1805_);
lean_dec_ref(v___x_1804_);
v_a_1947_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1832_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1832_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec(v_typesStx_1809_);
lean_dec(v_tk_1808_);
lean_dec(v___x_1807_);
lean_dec_ref(v___x_1806_);
lean_dec_ref(v___x_1805_);
lean_dec_ref(v___x_1804_);
lean_dec(v_a_1802_);
v_a_1956_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1821_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1821_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1800_ = stack[0].m_obj;
lean_object* v_a_1801_ = stack[1].m_obj;
lean_object* v_a_1802_ = stack[2].m_obj;
uint8_t v___x_1803_ = stack[3].m_num;
lean_object* v___x_1804_ = stack[4].m_obj;
lean_object* v___x_1805_ = stack[5].m_obj;
lean_object* v___x_1806_ = stack[6].m_obj;
lean_object* v___x_1807_ = stack[7].m_obj;
lean_object* v_tk_1808_ = stack[8].m_obj;
lean_object* v_typesStx_1809_ = stack[9].m_obj;
lean_object* v___x_1810_ = stack[10].m_obj;
lean_object* v___y_1811_ = stack[11].m_obj;
lean_object* v___y_1812_ = stack[12].m_obj;
lean_object* v___y_1813_ = stack[13].m_obj;
lean_object* v___y_1814_ = stack[14].m_obj;
lean_object* v___y_1815_ = stack[15].m_obj;
lean_object* v___y_1816_ = stack[16].m_obj;
lean_object* v___y_1817_ = stack[17].m_obj;
lean_object* v___y_1818_ = stack[18].m_obj;
lean_object* v___y_1819_ = stack[19].m_obj;
lean_object* v_res_1964_;
v_res_1964_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1(v___x_1800_, v_a_1801_, v_a_1802_, v___x_1803_, v___x_1804_, v___x_1805_, v___x_1806_, v___x_1807_, v_tk_1808_, v_typesStx_1809_, v___x_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
stack->m_obj
 = v_res_1964_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___boxed(lean_object** _args){
lean_object* v___x_1965_ = _args[0];
lean_object* v_a_1966_ = _args[1];
lean_object* v_a_1967_ = _args[2];
lean_object* v___x_1968_ = _args[3];
lean_object* v___x_1969_ = _args[4];
lean_object* v___x_1970_ = _args[5];
lean_object* v___x_1971_ = _args[6];
lean_object* v___x_1972_ = _args[7];
lean_object* v_tk_1973_ = _args[8];
lean_object* v_typesStx_1974_ = _args[9];
lean_object* v___x_1975_ = _args[10];
lean_object* v___y_1976_ = _args[11];
lean_object* v___y_1977_ = _args[12];
lean_object* v___y_1978_ = _args[13];
lean_object* v___y_1979_ = _args[14];
lean_object* v___y_1980_ = _args[15];
lean_object* v___y_1981_ = _args[16];
lean_object* v___y_1982_ = _args[17];
lean_object* v___y_1983_ = _args[18];
lean_object* v___y_1984_ = _args[19];
lean_object* v___y_1985_ = _args[20];
_start:
{
uint8_t v___x_54968__boxed_1986_; lean_object* v_res_1987_; 
v___x_54968__boxed_1986_ = lean_unbox(v___x_1968_);
v_res_1987_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1(v___x_1965_, v_a_1966_, v_a_1967_, v___x_54968__boxed_1986_, v___x_1969_, v___x_1970_, v___x_1971_, v___x_1972_, v_tk_1973_, v_typesStx_1974_, v___x_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec(v___x_1975_);
return v_res_1987_;
}
}
lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic(lean_object* v_x_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; 
v___x_2004_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0));
v___x_2005_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1));
v___x_2006_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1));
v___x_2007_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__1));
lean_inc(v_x_1994_);
v___x_2008_ = l_Lean_Syntax_isOfKind(v_x_1994_, v___x_2007_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; 
lean_dec(v_x_1994_);
v___x_2009_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2009_;
}
else
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; 
v___x_2010_ = lean_unsigned_to_nat(1u);
v___x_2011_ = l_Lean_Syntax_getArg(v_x_1994_, v___x_2010_);
v___x_2012_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_2011_);
v___x_2013_ = l_Lean_Syntax_isOfKind(v___x_2011_, v___x_2012_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; 
lean_dec(v___x_2011_);
lean_dec(v_x_1994_);
v___x_2014_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2014_;
}
else
{
lean_object* v___x_2015_; lean_object* v_tk_2016_; lean_object* v_typesStx_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___x_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; 
v___x_2015_ = lean_unsigned_to_nat(0u);
v_tk_2016_ = l_Lean_Syntax_getArg(v_x_1994_, v___x_2015_);
v___x_2105_ = lean_unsigned_to_nat(2u);
v___x_2106_ = l_Lean_Syntax_getArg(v_x_1994_, v___x_2105_);
lean_dec(v_x_1994_);
v___x_2107_ = l_Lean_Syntax_isNone(v___x_2106_);
if (v___x_2107_ == 0)
{
uint8_t v___x_2108_; 
lean_inc(v___x_2106_);
v___x_2108_ = l_Lean_Syntax_matchesNull(v___x_2106_, v___x_2010_);
if (v___x_2108_ == 0)
{
lean_object* v___x_2109_; 
lean_dec(v___x_2106_);
lean_dec(v_tk_2016_);
lean_dec(v___x_2011_);
v___x_2109_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2109_;
}
else
{
lean_object* v_typesStx_2110_; 
v_typesStx_2110_ = l_Lean_Syntax_getArg(v___x_2106_, v___x_2015_);
lean_dec(v___x_2106_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2113_; uint8_t v___x_2114_; 
v___x_2113_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_typesStx_2110_);
v___x_2114_ = l_Lean_Syntax_isOfKind(v_typesStx_2110_, v___x_2113_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; 
lean_dec(v_typesStx_2110_);
lean_dec(v_tk_2016_);
lean_dec(v___x_2011_);
v___x_2115_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2115_;
}
else
{
goto v___jp_2111_;
}
}
else
{
goto v___jp_2111_;
}
v___jp_2111_:
{
lean_object* v___x_2112_; 
v___x_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2112_, 0, v_typesStx_2110_);
v_typesStx_2018_ = v___x_2112_;
v___y_2019_ = v_a_1995_;
v___y_2020_ = v_a_1996_;
v___y_2021_ = v_a_1997_;
v___y_2022_ = v_a_1998_;
v___y_2023_ = v_a_1999_;
v___y_2024_ = v_a_2000_;
v___y_2025_ = v_a_2001_;
v___y_2026_ = v_a_2002_;
goto v___jp_2017_;
}
}
}
else
{
lean_object* v___x_2116_; 
lean_dec(v___x_2106_);
v___x_2116_ = lean_box(0);
v_typesStx_2018_ = v___x_2116_;
v___y_2019_ = v_a_1995_;
v___y_2020_ = v_a_1996_;
v___y_2021_ = v_a_1997_;
v___y_2022_ = v_a_1998_;
v___y_2023_ = v_a_1999_;
v___y_2024_ = v_a_2000_;
v___y_2025_ = v_a_2001_;
v___y_2026_ = v_a_2002_;
goto v___jp_2017_;
}
v___jp_2017_:
{
lean_object* v___x_2027_; 
v___x_2027_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_2025_, v___y_2026_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2103_; 
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2103_ == 0)
{
lean_object* v_unused_2104_; 
v_unused_2104_ = lean_ctor_get(v___x_2027_, 0);
lean_dec(v_unused_2104_);
v___x_2029_ = v___x_2027_;
v_isShared_2030_ = v_isSharedCheck_2103_;
goto v_resetjp_2028_;
}
else
{
lean_dec(v___x_2027_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2103_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2031_; uint8_t v___x_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2031_ = lean_unsigned_to_nat(10u);
v___x_2032_ = 0;
v___x_2033_ = lean_unsigned_to_nat(100000u);
v___x_2034_ = 0;
v___x_2035_ = lean_unsigned_to_nat(64u);
v___x_2036_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v___x_2036_, 0, v___x_2031_);
lean_ctor_set(v___x_2036_, 1, v___x_2033_);
lean_ctor_set(v___x_2036_, 2, v___x_2035_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*3, v___x_2013_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*3 + 1, v___x_2013_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*3 + 2, v___x_2032_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*3 + 3, v___x_2013_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*3 + 4, v___x_2013_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*3 + 5, v___x_2013_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*3 + 6, v___x_2013_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*3 + 7, v___x_2013_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*3 + 8, v___x_2032_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*3 + 9, v___x_2032_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*3 + 10, v___x_2034_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*3 + 11, v___x_2032_);
lean_inc(v___x_2011_);
v___x_2037_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_2011_, v___x_2036_, v___x_2013_, v___y_2019_, v___y_2025_, v___y_2026_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2039_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2038_);
lean_dec_ref_known(v___x_2037_, 1);
lean_inc(v_typesStx_2018_);
v___x_2039_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_2018_, v_a_2038_, v___y_2025_, v___y_2026_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2041_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2039_, 1);
v___x_2041_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(v_a_2038_, v_a_2040_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2043_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___x_2041_, 1);
v___x_2043_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2020_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2043_, 1);
v___x_2045_ = lean_unsigned_to_nat(9u);
v___x_2046_ = lean_unsigned_to_nat(5u);
v___x_2047_ = lean_unsigned_to_nat(8u);
v___x_2048_ = lean_unsigned_to_nat(1000u);
v___x_2049_ = lean_unsigned_to_nat(1024u);
v___x_2050_ = lean_unsigned_to_nat(10000u);
v___x_2051_ = lean_unsigned_to_nat(1048576u);
v___x_2052_ = lean_unsigned_to_nat(50u);
v___x_2053_ = lean_box(0);
v___x_2054_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_2054_, 0, v___x_2045_);
lean_ctor_set(v___x_2054_, 1, v___x_2046_);
lean_ctor_set(v___x_2054_, 2, v___x_2047_);
lean_ctor_set(v___x_2054_, 3, v___x_2047_);
lean_ctor_set(v___x_2054_, 4, v___x_2048_);
lean_ctor_set(v___x_2054_, 5, v___x_2048_);
lean_ctor_set(v___x_2054_, 6, v___x_2033_);
lean_ctor_set(v___x_2054_, 7, v___x_2049_);
lean_ctor_set(v___x_2054_, 8, v___x_2050_);
lean_ctor_set(v___x_2054_, 9, v___x_2048_);
lean_ctor_set(v___x_2054_, 10, v___x_2051_);
lean_ctor_set(v___x_2054_, 11, v___x_2031_);
lean_ctor_set(v___x_2054_, 12, v___x_2052_);
lean_ctor_set(v___x_2054_, 13, v___x_2053_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14, v___x_2032_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 1, v___x_2032_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 2, v___x_2032_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 3, v___x_2032_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 4, v___x_2032_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 5, v___x_2013_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 6, v___x_2013_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 7, v___x_2013_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 8, v___x_2032_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 9, v___x_2032_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 10, v___x_2013_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 11, v___x_2032_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 12, v___x_2013_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 13, v___x_2013_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 14, v___x_2013_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 15, v___x_2013_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 16, v___x_2013_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 17, v___x_2032_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 18, v___x_2013_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 19, v___x_2013_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 20, v___x_2013_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 21, v___x_2013_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 22, v___x_2013_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 23, v___x_2013_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 24, v___x_2013_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 25, v___x_2013_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 26, v___x_2013_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 27, v___x_2013_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 28, v___x_2013_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 29, v___x_2013_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 30, v___x_2032_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 31, v___x_2013_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*14 + 32, v___x_2013_);
v___x_2055_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_2054_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2058_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___x_2055_, 1);
lean_inc(v_a_2044_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 0, v_a_2044_);
v___x_2058_ = v___x_2029_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2044_);
v___x_2058_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2059_; lean_object* v___f_2060_; lean_object* v___x_2061_; 
v___x_2059_ = lean_box(v___x_2032_);
v___f_2060_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___boxed), 21, 11);
lean_closure_set(v___f_2060_, 0, v___x_2058_);
lean_closure_set(v___f_2060_, 1, v_a_2042_);
lean_closure_set(v___f_2060_, 2, v_a_2044_);
lean_closure_set(v___f_2060_, 3, v___x_2059_);
lean_closure_set(v___f_2060_, 4, v___x_2004_);
lean_closure_set(v___f_2060_, 5, v___x_2005_);
lean_closure_set(v___f_2060_, 6, v___x_2006_);
lean_closure_set(v___f_2060_, 7, v___x_2011_);
lean_closure_set(v___f_2060_, 8, v_tk_2016_);
lean_closure_set(v___f_2060_, 9, v_typesStx_2018_);
lean_closure_set(v___f_2060_, 10, v___x_2015_);
v___x_2061_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___f_2060_, v_a_2056_, v___x_2053_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
return v___x_2061_;
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec(v_a_2044_);
lean_dec(v_a_2042_);
lean_del_object(v___x_2029_);
lean_dec(v_typesStx_2018_);
lean_dec(v_tk_2016_);
lean_dec(v___x_2011_);
v_a_2063_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2055_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2055_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_dec(v_a_2042_);
lean_del_object(v___x_2029_);
lean_dec(v_typesStx_2018_);
lean_dec(v_tk_2016_);
lean_dec(v___x_2011_);
v_a_2071_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2043_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2043_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_del_object(v___x_2029_);
lean_dec(v_typesStx_2018_);
lean_dec(v_tk_2016_);
lean_dec(v___x_2011_);
v_a_2079_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2041_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2041_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec(v_a_2038_);
lean_del_object(v___x_2029_);
lean_dec(v_typesStx_2018_);
lean_dec(v_tk_2016_);
lean_dec(v___x_2011_);
v_a_2087_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2039_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2039_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_del_object(v___x_2029_);
lean_dec(v_typesStx_2018_);
lean_dec(v_tk_2016_);
lean_dec(v___x_2011_);
v_a_2095_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2037_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2037_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
}
else
{
lean_dec(v_typesStx_2018_);
lean_dec(v_tk_2016_);
lean_dec(v___x_2011_);
return v___x_2027_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1994_ = stack[0].m_obj;
lean_object* v_a_1995_ = stack[1].m_obj;
lean_object* v_a_1996_ = stack[2].m_obj;
lean_object* v_a_1997_ = stack[3].m_obj;
lean_object* v_a_1998_ = stack[4].m_obj;
lean_object* v_a_1999_ = stack[5].m_obj;
lean_object* v_a_2000_ = stack[6].m_obj;
lean_object* v_a_2001_ = stack[7].m_obj;
lean_object* v_a_2002_ = stack[8].m_obj;
lean_object* v_res_2117_;
v_res_2117_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic(v_x_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
stack->m_obj
 = v_res_2117_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___boxed(lean_object* v_x_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic(v_x_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec(v_a_2122_);
lean_dec_ref(v_a_2121_);
lean_dec(v_a_2120_);
lean_dec_ref(v_a_2119_);
return v_res_2128_;
}
}
lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1(){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2137_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2138_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__1));
v___x_2139_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___closed__1));
v___x_2140_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___boxed), 10, 0);
v___x_2141_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2137_, v___x_2138_, v___x_2139_, v___x_2140_);
return v___x_2141_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2142_;
v_res_2142_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1();
stack->m_obj
 = v_res_2142_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___boxed(lean_object* v_a_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1();
return v_res_2144_;
}
}
uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_2151_, uint8_t v___y_2152_, lean_object* v_x_2153_){
_start:
{
if (lean_obj_tag(v_x_2153_) == 1)
{
lean_object* v_pre_2154_; 
v_pre_2154_ = lean_ctor_get(v_x_2153_, 0);
switch(lean_obj_tag(v_pre_2154_))
{
case 1:
{
lean_object* v_pre_2155_; 
v_pre_2155_ = lean_ctor_get(v_pre_2154_, 0);
switch(lean_obj_tag(v_pre_2155_))
{
case 0:
{
lean_object* v_str_2156_; lean_object* v_str_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; 
v_str_2156_ = lean_ctor_get(v_x_2153_, 1);
v_str_2157_ = lean_ctor_get(v_pre_2154_, 1);
v___x_2158_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__0));
v___x_2159_ = lean_string_dec_eq(v_str_2157_, v___x_2158_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; uint8_t v___x_2161_; 
v___x_2160_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1));
v___x_2161_ = lean_string_dec_eq(v_str_2157_, v___x_2160_);
if (v___x_2161_ == 0)
{
return v___x_2161_;
}
else
{
lean_object* v___x_2162_; uint8_t v___x_2163_; 
v___x_2162_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_2163_ = lean_string_dec_eq(v_str_2156_, v___x_2162_);
if (v___x_2163_ == 0)
{
return v___x_2163_;
}
else
{
return v_suppressElabErrors_2151_;
}
}
}
else
{
lean_object* v___x_2164_; uint8_t v___x_2165_; 
v___x_2164_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_2165_ = lean_string_dec_eq(v_str_2156_, v___x_2164_);
if (v___x_2165_ == 0)
{
return v___x_2165_;
}
else
{
return v_suppressElabErrors_2151_;
}
}
}
case 1:
{
lean_object* v_pre_2166_; 
v_pre_2166_ = lean_ctor_get(v_pre_2155_, 0);
if (lean_obj_tag(v_pre_2166_) == 0)
{
lean_object* v_str_2167_; lean_object* v_str_2168_; lean_object* v_str_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; 
v_str_2167_ = lean_ctor_get(v_x_2153_, 1);
v_str_2168_ = lean_ctor_get(v_pre_2154_, 1);
v_str_2169_ = lean_ctor_get(v_pre_2155_, 1);
v___x_2170_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_2171_ = lean_string_dec_eq(v_str_2169_, v___x_2170_);
if (v___x_2171_ == 0)
{
return v___x_2171_;
}
else
{
lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2172_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_2173_ = lean_string_dec_eq(v_str_2168_, v___x_2172_);
if (v___x_2173_ == 0)
{
return v___x_2173_;
}
else
{
lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2174_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_2175_ = lean_string_dec_eq(v_str_2167_, v___x_2174_);
if (v___x_2175_ == 0)
{
return v___x_2175_;
}
else
{
return v_suppressElabErrors_2151_;
}
}
}
}
else
{
return v___y_2152_;
}
}
default: 
{
return v___y_2152_;
}
}
}
case 0:
{
lean_object* v_str_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; 
v_str_2176_ = lean_ctor_get(v_x_2153_, 1);
v___x_2177_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_2178_ = lean_string_dec_eq(v_str_2176_, v___x_2177_);
if (v___x_2178_ == 0)
{
return v___x_2178_;
}
else
{
return v_suppressElabErrors_2151_;
}
}
default: 
{
return v___y_2152_;
}
}
}
else
{
return v___y_2152_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_2151_ = stack[0].m_num;
uint8_t v___y_2152_ = stack[1].m_num;
lean_object* v_x_2153_ = stack[2].m_obj;
uint8_t v_res_2179_;
v_res_2179_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_2151_, v___y_2152_, v_x_2153_);
stack->m_num = v_res_2179_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_2180_, lean_object* v___y_2181_, lean_object* v_x_2182_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2183_; uint8_t v___y_7492__boxed_2184_; uint8_t v_res_2185_; lean_object* v_r_2186_; 
v_suppressElabErrors_boxed_2183_ = lean_unbox(v_suppressElabErrors_2180_);
v___y_7492__boxed_2184_ = lean_unbox(v___y_2181_);
v_res_2185_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_2183_, v___y_7492__boxed_2184_, v_x_2182_);
lean_dec(v_x_2182_);
v_r_2186_ = lean_box(v_res_2185_);
return v_r_2186_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(lean_object* v_ref_2187_, lean_object* v_msgData_2188_, uint8_t v_severity_2189_, uint8_t v_isSilent_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v___y_2197_; lean_object* v___y_2198_; uint8_t v___y_2199_; uint8_t v___y_2200_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v_toCold_2204_; lean_object* v___y_2205_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; uint8_t v___y_2238_; uint8_t v___y_2239_; uint8_t v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2261_; lean_object* v___y_2262_; uint8_t v___y_2263_; uint8_t v___y_2264_; uint8_t v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; uint8_t v___y_2271_; uint8_t v___y_2272_; uint8_t v___y_2273_; uint8_t v___x_2284_; uint8_t v___y_2286_; uint8_t v___y_2287_; uint8_t v___y_2288_; uint8_t v___y_2290_; uint8_t v___x_2298_; 
v___x_2284_ = 2;
v___x_2298_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2189_, v___x_2284_);
if (v___x_2298_ == 0)
{
v___y_2290_ = v___x_2298_;
goto v___jp_2289_;
}
else
{
uint8_t v___x_2299_; 
lean_inc_ref(v_msgData_2188_);
v___x_2299_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2188_);
v___y_2290_ = v___x_2299_;
goto v___jp_2289_;
}
v___jp_2196_:
{
lean_object* v_currNamespace_2206_; lean_object* v_openDecls_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v_env_2212_; lean_object* v_nextMacroScope_2213_; lean_object* v_ngen_2214_; lean_object* v_auxDeclNGen_2215_; lean_object* v_traceState_2216_; lean_object* v_cache_2217_; lean_object* v_recordedDeps_2218_; lean_object* v_messages_2219_; lean_object* v_infoState_2220_; lean_object* v_snapshotTasks_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2232_; 
v_currNamespace_2206_ = lean_ctor_get(v_toCold_2204_, 4);
v_openDecls_2207_ = lean_ctor_get(v_toCold_2204_, 5);
lean_inc(v_openDecls_2207_);
lean_inc(v_currNamespace_2206_);
v___x_2208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2208_, 0, v_currNamespace_2206_);
lean_ctor_set(v___x_2208_, 1, v_openDecls_2207_);
v___x_2209_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
lean_ctor_set(v___x_2209_, 1, v___y_2203_);
lean_inc_ref(v___y_2202_);
lean_inc_ref(v___y_2197_);
v___x_2210_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2210_, 0, v___y_2197_);
lean_ctor_set(v___x_2210_, 1, v___y_2201_);
lean_ctor_set(v___x_2210_, 2, v___y_2198_);
lean_ctor_set(v___x_2210_, 3, v___y_2202_);
lean_ctor_set(v___x_2210_, 4, v___x_2209_);
lean_ctor_set_uint8(v___x_2210_, sizeof(void*)*5, v___y_2200_);
lean_ctor_set_uint8(v___x_2210_, sizeof(void*)*5 + 1, v___y_2199_);
lean_ctor_set_uint8(v___x_2210_, sizeof(void*)*5 + 2, v_isSilent_2190_);
v___x_2211_ = lean_st_ref_take(v___y_2205_);
v_env_2212_ = lean_ctor_get(v___x_2211_, 0);
v_nextMacroScope_2213_ = lean_ctor_get(v___x_2211_, 1);
v_ngen_2214_ = lean_ctor_get(v___x_2211_, 2);
v_auxDeclNGen_2215_ = lean_ctor_get(v___x_2211_, 3);
v_traceState_2216_ = lean_ctor_get(v___x_2211_, 4);
v_cache_2217_ = lean_ctor_get(v___x_2211_, 5);
v_recordedDeps_2218_ = lean_ctor_get(v___x_2211_, 6);
v_messages_2219_ = lean_ctor_get(v___x_2211_, 7);
v_infoState_2220_ = lean_ctor_get(v___x_2211_, 8);
v_snapshotTasks_2221_ = lean_ctor_get(v___x_2211_, 9);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2223_ = v___x_2211_;
v_isShared_2224_ = v_isSharedCheck_2232_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_snapshotTasks_2221_);
lean_inc(v_infoState_2220_);
lean_inc(v_messages_2219_);
lean_inc(v_recordedDeps_2218_);
lean_inc(v_cache_2217_);
lean_inc(v_traceState_2216_);
lean_inc(v_auxDeclNGen_2215_);
lean_inc(v_ngen_2214_);
lean_inc(v_nextMacroScope_2213_);
lean_inc(v_env_2212_);
lean_dec(v___x_2211_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2232_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2228_; 
v___x_2225_ = lean_box(0);
v___x_2226_ = l_Lean_MessageLog_add(v___x_2210_, v_messages_2219_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 7, v___x_2226_);
v___x_2228_ = v___x_2223_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_env_2212_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_nextMacroScope_2213_);
lean_ctor_set(v_reuseFailAlloc_2231_, 2, v_ngen_2214_);
lean_ctor_set(v_reuseFailAlloc_2231_, 3, v_auxDeclNGen_2215_);
lean_ctor_set(v_reuseFailAlloc_2231_, 4, v_traceState_2216_);
lean_ctor_set(v_reuseFailAlloc_2231_, 5, v_cache_2217_);
lean_ctor_set(v_reuseFailAlloc_2231_, 6, v_recordedDeps_2218_);
lean_ctor_set(v_reuseFailAlloc_2231_, 7, v___x_2226_);
lean_ctor_set(v_reuseFailAlloc_2231_, 8, v_infoState_2220_);
lean_ctor_set(v_reuseFailAlloc_2231_, 9, v_snapshotTasks_2221_);
v___x_2228_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = lean_st_ref_put(v___y_2205_, v___x_2228_);
v___x_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2225_);
return v___x_2230_;
}
}
}
v___jp_2233_:
{
lean_object* v_fileName_2242_; lean_object* v_fileMap_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2259_; 
v_fileName_2242_ = lean_ctor_get(v___y_2237_, 0);
v_fileMap_2243_ = lean_ctor_get(v___y_2237_, 1);
v___x_2244_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2188_);
v___x_2245_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v___x_2244_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2248_ = v___x_2245_;
v_isShared_2249_ = v_isSharedCheck_2259_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2245_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2259_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
lean_inc_ref_n(v_fileMap_2243_, 2);
v___x_2250_ = l_Lean_FileMap_toPosition(v_fileMap_2243_, v___y_2236_);
lean_dec(v___y_2236_);
v___x_2251_ = l_Lean_FileMap_toPosition(v_fileMap_2243_, v___y_2241_);
lean_dec(v___y_2241_);
v___x_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
v___x_2253_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5));
if (v___y_2239_ == 0)
{
lean_del_object(v___x_2248_);
lean_dec_ref(v___y_2235_);
v___y_2197_ = v_fileName_2242_;
v___y_2198_ = v___x_2252_;
v___y_2199_ = v___y_2238_;
v___y_2200_ = v___y_2240_;
v___y_2201_ = v___x_2250_;
v___y_2202_ = v___x_2253_;
v___y_2203_ = v_a_2246_;
v_toCold_2204_ = v___y_2234_;
v___y_2205_ = v___y_2194_;
goto v___jp_2196_;
}
else
{
uint8_t v___x_2254_; 
lean_inc(v_a_2246_);
v___x_2254_ = l_Lean_MessageData_hasTag(v___y_2235_, v_a_2246_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; lean_object* v___x_2257_; 
lean_dec_ref_known(v___x_2252_, 1);
lean_dec_ref(v___x_2250_);
lean_dec(v_a_2246_);
v___x_2255_ = lean_box(0);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 0, v___x_2255_);
v___x_2257_ = v___x_2248_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2255_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
else
{
lean_del_object(v___x_2248_);
v___y_2197_ = v_fileName_2242_;
v___y_2198_ = v___x_2252_;
v___y_2199_ = v___y_2238_;
v___y_2200_ = v___y_2240_;
v___y_2201_ = v___x_2250_;
v___y_2202_ = v___x_2253_;
v___y_2203_ = v_a_2246_;
v_toCold_2204_ = v___y_2234_;
v___y_2205_ = v___y_2194_;
goto v___jp_2196_;
}
}
}
}
v___jp_2260_:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_Syntax_getTailPos_x3f(v___y_2266_, v___y_2265_);
lean_dec(v___y_2266_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_inc(v___y_2267_);
v___y_2234_ = v___y_2261_;
v___y_2235_ = v___y_2262_;
v___y_2236_ = v___y_2267_;
v___y_2237_ = v___y_2261_;
v___y_2238_ = v___y_2264_;
v___y_2239_ = v___y_2263_;
v___y_2240_ = v___y_2265_;
v___y_2241_ = v___y_2267_;
goto v___jp_2233_;
}
else
{
lean_object* v_val_2269_; 
v_val_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_val_2269_);
lean_dec_ref_known(v___x_2268_, 1);
v___y_2234_ = v___y_2261_;
v___y_2235_ = v___y_2262_;
v___y_2236_ = v___y_2267_;
v___y_2237_ = v___y_2261_;
v___y_2238_ = v___y_2264_;
v___y_2239_ = v___y_2263_;
v___y_2240_ = v___y_2265_;
v___y_2241_ = v_val_2269_;
goto v___jp_2233_;
}
}
v___jp_2270_:
{
lean_object* v_toCold_2274_; lean_object* v_ref_2275_; uint8_t v_suppressElabErrors_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___f_2279_; lean_object* v_ref_2280_; lean_object* v___x_2281_; 
v_toCold_2274_ = lean_ctor_get(v___y_2193_, 0);
v_ref_2275_ = lean_ctor_get(v___y_2193_, 2);
v_suppressElabErrors_2276_ = lean_ctor_get_uint8(v___y_2193_, sizeof(void*)*3 + 2);
v___x_2277_ = lean_box(v_suppressElabErrors_2276_);
v___x_2278_ = lean_box(v___y_2271_);
v___f_2279_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2279_, 0, v___x_2277_);
lean_closure_set(v___f_2279_, 1, v___x_2278_);
v_ref_2280_ = l_Lean_replaceRef(v_ref_2187_, v_ref_2275_);
v___x_2281_ = l_Lean_Syntax_getPos_x3f(v_ref_2280_, v___y_2272_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v___x_2282_; 
v___x_2282_ = lean_unsigned_to_nat(0u);
v___y_2261_ = v_toCold_2274_;
v___y_2262_ = v___f_2279_;
v___y_2263_ = v_suppressElabErrors_2276_;
v___y_2264_ = v___y_2273_;
v___y_2265_ = v___y_2272_;
v___y_2266_ = v_ref_2280_;
v___y_2267_ = v___x_2282_;
goto v___jp_2260_;
}
else
{
lean_object* v_val_2283_; 
v_val_2283_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_val_2283_);
lean_dec_ref_known(v___x_2281_, 1);
v___y_2261_ = v_toCold_2274_;
v___y_2262_ = v___f_2279_;
v___y_2263_ = v_suppressElabErrors_2276_;
v___y_2264_ = v___y_2273_;
v___y_2265_ = v___y_2272_;
v___y_2266_ = v_ref_2280_;
v___y_2267_ = v_val_2283_;
goto v___jp_2260_;
}
}
v___jp_2285_:
{
if (v___y_2288_ == 0)
{
v___y_2271_ = v___y_2286_;
v___y_2272_ = v___y_2287_;
v___y_2273_ = v_severity_2189_;
goto v___jp_2270_;
}
else
{
v___y_2271_ = v___y_2286_;
v___y_2272_ = v___y_2287_;
v___y_2273_ = v___x_2284_;
goto v___jp_2270_;
}
}
v___jp_2289_:
{
if (v___y_2290_ == 0)
{
uint8_t v___x_2291_; uint8_t v___x_2292_; 
v___x_2291_ = 1;
v___x_2292_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2189_, v___x_2291_);
if (v___x_2292_ == 0)
{
v___y_2286_ = v___y_2290_;
v___y_2287_ = v___y_2290_;
v___y_2288_ = v___x_2292_;
goto v___jp_2285_;
}
else
{
lean_object* v___x_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v___x_2293_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2193_);
v___x_2294_ = l_Lean_warningAsError;
v___x_2295_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v___x_2293_, v___x_2294_);
lean_dec_ref(v___x_2293_);
v___y_2286_ = v___y_2290_;
v___y_2287_ = v___y_2290_;
v___y_2288_ = v___x_2295_;
goto v___jp_2285_;
}
}
else
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
lean_dec_ref(v_msgData_2188_);
v___x_2296_ = lean_box(0);
v___x_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
return v___x_2297_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2187_ = stack[0].m_obj;
lean_object* v_msgData_2188_ = stack[1].m_obj;
uint8_t v_severity_2189_ = stack[2].m_num;
uint8_t v_isSilent_2190_ = stack[3].m_num;
lean_object* v___y_2191_ = stack[4].m_obj;
lean_object* v___y_2192_ = stack[5].m_obj;
lean_object* v___y_2193_ = stack[6].m_obj;
lean_object* v___y_2194_ = stack[7].m_obj;
lean_object* v_res_2300_;
v_res_2300_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(v_ref_2187_, v_msgData_2188_, v_severity_2189_, v_isSilent_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
stack->m_obj
 = v_res_2300_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_2301_, lean_object* v_msgData_2302_, lean_object* v_severity_2303_, lean_object* v_isSilent_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
uint8_t v_severity_boxed_2310_; uint8_t v_isSilent_boxed_2311_; lean_object* v_res_2312_; 
v_severity_boxed_2310_ = lean_unbox(v_severity_2303_);
v_isSilent_boxed_2311_ = lean_unbox(v_isSilent_2304_);
v_res_2312_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(v_ref_2301_, v_msgData_2302_, v_severity_boxed_2310_, v_isSilent_boxed_2311_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v_ref_2301_);
return v_res_2312_;
}
}
lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(lean_object* v_msgData_2313_, uint8_t v_severity_2314_, uint8_t v_isSilent_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v_ref_2321_; lean_object* v___x_2322_; 
v_ref_2321_ = lean_ctor_get(v___y_2318_, 2);
v___x_2322_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(v_ref_2321_, v_msgData_2313_, v_severity_2314_, v_isSilent_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
return v___x_2322_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2313_ = stack[0].m_obj;
uint8_t v_severity_2314_ = stack[1].m_num;
uint8_t v_isSilent_2315_ = stack[2].m_num;
lean_object* v___y_2316_ = stack[3].m_obj;
lean_object* v___y_2317_ = stack[4].m_obj;
lean_object* v___y_2318_ = stack[5].m_obj;
lean_object* v___y_2319_ = stack[6].m_obj;
lean_object* v_res_2323_;
v_res_2323_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(v_msgData_2313_, v_severity_2314_, v_isSilent_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
stack->m_obj
 = v_res_2323_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0___boxed(lean_object* v_msgData_2324_, lean_object* v_severity_2325_, lean_object* v_isSilent_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
uint8_t v_severity_boxed_2332_; uint8_t v_isSilent_boxed_2333_; lean_object* v_res_2334_; 
v_severity_boxed_2332_ = lean_unbox(v_severity_2325_);
v_isSilent_boxed_2333_ = lean_unbox(v_isSilent_2326_);
v_res_2334_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(v_msgData_2324_, v_severity_boxed_2332_, v_isSilent_boxed_2333_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
return v_res_2334_;
}
}
lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(lean_object* v_msgData_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
uint8_t v___x_2341_; uint8_t v___x_2342_; lean_object* v___x_2343_; 
v___x_2341_ = 1;
v___x_2342_ = 0;
v___x_2343_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(v_msgData_2335_, v___x_2341_, v___x_2342_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
return v___x_2343_;
}
}
LEAN_EXPORT void l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2335_ = stack[0].m_obj;
lean_object* v___y_2336_ = stack[1].m_obj;
lean_object* v___y_2337_ = stack[2].m_obj;
lean_object* v___y_2338_ = stack[3].m_obj;
lean_object* v___y_2339_ = stack[4].m_obj;
lean_object* v_res_2344_;
v_res_2344_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(v_msgData_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
stack->m_obj
 = v_res_2344_;
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0___boxed(lean_object* v_msgData_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(v_msgData_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
return v_res_2351_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2356_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__2));
v___x_2357_ = l_Lean_stringToMessageData(v___x_2356_);
return v___x_2357_;
}
}
lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0(lean_object* v___x_2358_, lean_object* v___x_2359_, lean_object* v___x_2360_, lean_object* v___x_2361_, lean_object* v_tk_2362_, lean_object* v_typesStx_2363_, lean_object* v___x_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v_ref_2370_; uint8_t v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___y_2381_; 
v_ref_2370_ = lean_ctor_get(v___y_2367_, 2);
v___x_2371_ = 0;
v___x_2372_ = l_Lean_SourceInfo_fromRef(v_ref_2370_, v___x_2371_);
v___x_2373_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1));
v___x_2374_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__0));
v___x_2375_ = l_Lean_Name_mkStr4(v___x_2358_, v___x_2359_, v___x_2360_, v___x_2374_);
v___x_2376_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__1));
lean_inc(v___x_2372_);
v___x_2377_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2372_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
v___x_2378_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3));
v___x_2379_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__4);
if (lean_obj_tag(v_typesStx_2363_) == 1)
{
lean_object* v_val_2402_; lean_object* v___x_2403_; 
v_val_2402_ = lean_ctor_get(v_typesStx_2363_, 0);
lean_inc(v_val_2402_);
lean_dec_ref_known(v_typesStx_2363_, 1);
v___x_2403_ = l_Array_mkArray1___redArg(v_val_2402_);
v___y_2381_ = v___x_2403_;
goto v___jp_2380_;
}
else
{
lean_object* v___x_2404_; 
lean_dec(v_typesStx_2363_);
v___x_2404_ = lean_mk_empty_array_with_capacity(v___x_2364_);
v___y_2381_ = v___x_2404_;
goto v___jp_2380_;
}
v___jp_2380_:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2382_ = l_Array_append___redArg(v___x_2379_, v___y_2381_);
lean_dec_ref(v___y_2381_);
lean_inc(v___x_2372_);
v___x_2383_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2372_);
lean_ctor_set(v___x_2383_, 1, v___x_2378_);
lean_ctor_set(v___x_2383_, 2, v___x_2382_);
v___x_2384_ = l_Lean_Syntax_node3(v___x_2372_, v___x_2375_, v___x_2377_, v___x_2361_, v___x_2383_);
v___x_2385_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__3, &l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__3);
v___x_2386_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(v___x_2385_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2400_; 
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2400_ == 0)
{
lean_object* v_unused_2401_; 
v_unused_2401_ = lean_ctor_get(v___x_2386_, 0);
lean_dec(v_unused_2401_);
v___x_2388_ = v___x_2386_;
v_isShared_2389_ = v_isSharedCheck_2400_;
goto v_resetjp_2387_;
}
else
{
lean_dec(v___x_2386_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2400_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2394_; 
v___x_2390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2373_);
lean_ctor_set(v___x_2390_, 1, v___x_2384_);
v___x_2391_ = lean_box(0);
v___x_2392_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2390_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
lean_ctor_set(v___x_2392_, 2, v___x_2391_);
lean_ctor_set(v___x_2392_, 3, v___x_2391_);
lean_ctor_set(v___x_2392_, 4, v___x_2391_);
lean_ctor_set(v___x_2392_, 5, v___x_2391_);
lean_inc(v_ref_2370_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set_tag(v___x_2388_, 1);
lean_ctor_set(v___x_2388_, 0, v_ref_2370_);
v___x_2394_ = v___x_2388_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_ref_2370_);
v___x_2394_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
lean_object* v___x_2395_; uint8_t v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2395_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__1___closed__2));
v___x_2396_ = 4;
v___x_2397_ = l_Lean_MessageData_nil;
v___x_2398_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2362_, v___x_2392_, v___x_2394_, v___x_2395_, v___x_2391_, v___x_2396_, v___x_2397_, v___y_2367_, v___y_2368_);
return v___x_2398_;
}
}
}
else
{
lean_dec(v___x_2384_);
lean_dec(v_tk_2362_);
return v___x_2386_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2358_ = stack[0].m_obj;
lean_object* v___x_2359_ = stack[1].m_obj;
lean_object* v___x_2360_ = stack[2].m_obj;
lean_object* v___x_2361_ = stack[3].m_obj;
lean_object* v_tk_2362_ = stack[4].m_obj;
lean_object* v_typesStx_2363_ = stack[5].m_obj;
lean_object* v___x_2364_ = stack[6].m_obj;
lean_object* v___y_2365_ = stack[7].m_obj;
lean_object* v___y_2366_ = stack[8].m_obj;
lean_object* v___y_2367_ = stack[9].m_obj;
lean_object* v___y_2368_ = stack[10].m_obj;
lean_object* v_res_2405_;
v_res_2405_ = l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0(v___x_2358_, v___x_2359_, v___x_2360_, v___x_2361_, v_tk_2362_, v_typesStx_2363_, v___x_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
stack->m_obj
 = v_res_2405_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___boxed(lean_object* v___x_2406_, lean_object* v___x_2407_, lean_object* v___x_2408_, lean_object* v___x_2409_, lean_object* v_tk_2410_, lean_object* v_typesStx_2411_, lean_object* v___x_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0(v___x_2406_, v___x_2407_, v___x_2408_, v___x_2409_, v_tk_2410_, v_typesStx_2411_, v___x_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___x_2412_);
return v_res_2418_;
}
}
lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic(lean_object* v_x_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; uint8_t v___x_2441_; 
v___x_2437_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0));
v___x_2438_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1));
v___x_2439_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1));
v___x_2440_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0));
lean_inc(v_x_2427_);
v___x_2441_ = l_Lean_Syntax_isOfKind(v_x_2427_, v___x_2440_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; 
lean_dec(v_x_2427_);
v___x_2442_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2442_;
}
else
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; uint8_t v___x_2446_; 
v___x_2443_ = lean_unsigned_to_nat(1u);
v___x_2444_ = l_Lean_Syntax_getArg(v_x_2427_, v___x_2443_);
v___x_2445_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_2444_);
v___x_2446_ = l_Lean_Syntax_isOfKind(v___x_2444_, v___x_2445_);
if (v___x_2446_ == 0)
{
lean_object* v___x_2447_; 
lean_dec(v___x_2444_);
lean_dec(v_x_2427_);
v___x_2447_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2447_;
}
else
{
lean_object* v___x_2448_; lean_object* v_tk_2449_; lean_object* v_typesStx_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___x_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; 
v___x_2448_ = lean_unsigned_to_nat(0u);
v_tk_2449_ = l_Lean_Syntax_getArg(v_x_2427_, v___x_2448_);
v___x_2544_ = lean_unsigned_to_nat(2u);
v___x_2545_ = l_Lean_Syntax_getArg(v_x_2427_, v___x_2544_);
v___x_2546_ = l_Lean_Syntax_isNone(v___x_2545_);
if (v___x_2546_ == 0)
{
uint8_t v___x_2547_; 
lean_inc(v___x_2545_);
v___x_2547_ = l_Lean_Syntax_matchesNull(v___x_2545_, v___x_2443_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; 
lean_dec(v___x_2545_);
lean_dec(v_tk_2449_);
lean_dec(v___x_2444_);
lean_dec(v_x_2427_);
v___x_2548_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2548_;
}
else
{
lean_object* v_typesStx_2549_; 
v_typesStx_2549_ = l_Lean_Syntax_getArg(v___x_2545_, v___x_2448_);
lean_dec(v___x_2545_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2552_; uint8_t v___x_2553_; 
v___x_2552_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_typesStx_2549_);
v___x_2553_ = l_Lean_Syntax_isOfKind(v_typesStx_2549_, v___x_2552_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; 
lean_dec(v_typesStx_2549_);
lean_dec(v_tk_2449_);
lean_dec(v___x_2444_);
lean_dec(v_x_2427_);
v___x_2554_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2554_;
}
else
{
goto v___jp_2550_;
}
}
else
{
goto v___jp_2550_;
}
v___jp_2550_:
{
lean_object* v___x_2551_; 
v___x_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2551_, 0, v_typesStx_2549_);
v_typesStx_2451_ = v___x_2551_;
v___y_2452_ = v_a_2428_;
v___y_2453_ = v_a_2429_;
v___y_2454_ = v_a_2430_;
v___y_2455_ = v_a_2431_;
v___y_2456_ = v_a_2432_;
v___y_2457_ = v_a_2433_;
v___y_2458_ = v_a_2434_;
v___y_2459_ = v_a_2435_;
goto v___jp_2450_;
}
}
}
else
{
lean_object* v___x_2555_; 
lean_dec(v___x_2545_);
v___x_2555_ = lean_box(0);
v_typesStx_2451_ = v___x_2555_;
v___y_2452_ = v_a_2428_;
v___y_2453_ = v_a_2429_;
v___y_2454_ = v_a_2430_;
v___y_2455_ = v_a_2431_;
v___y_2456_ = v_a_2432_;
v___y_2457_ = v_a_2433_;
v___y_2458_ = v_a_2434_;
v___y_2459_ = v_a_2435_;
goto v___jp_2450_;
}
v___jp_2450_:
{
lean_object* v___x_2460_; lean_object* v_path_2461_; lean_object* v___x_2462_; uint8_t v___x_2463_; 
v___x_2460_ = lean_unsigned_to_nat(3u);
v_path_2461_ = l_Lean_Syntax_getArg(v_x_2427_, v___x_2460_);
lean_dec(v_x_2427_);
v___x_2462_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__2));
lean_inc(v_path_2461_);
v___x_2463_ = l_Lean_Syntax_isOfKind(v_path_2461_, v___x_2462_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; 
lean_dec(v_path_2461_);
lean_dec(v_typesStx_2451_);
lean_dec(v_tk_2449_);
lean_dec(v___x_2444_);
v___x_2464_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2464_;
}
else
{
lean_object* v___f_2465_; lean_object* v___x_2466_; 
lean_inc(v_typesStx_2451_);
lean_inc(v___x_2444_);
v___f_2465_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___boxed), 12, 7);
lean_closure_set(v___f_2465_, 0, v___x_2437_);
lean_closure_set(v___f_2465_, 1, v___x_2438_);
lean_closure_set(v___f_2465_, 2, v___x_2439_);
lean_closure_set(v___f_2465_, 3, v___x_2444_);
lean_closure_set(v___f_2465_, 4, v_tk_2449_);
lean_closure_set(v___f_2465_, 5, v_typesStx_2451_);
lean_closure_set(v___f_2465_, 6, v___x_2448_);
v___x_2466_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_2458_, v___y_2459_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2542_; 
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2542_ == 0)
{
lean_object* v_unused_2543_; 
v_unused_2543_ = lean_ctor_get(v___x_2466_, 0);
lean_dec(v_unused_2543_);
v___x_2468_ = v___x_2466_;
v_isShared_2469_ = v_isSharedCheck_2542_;
goto v_resetjp_2467_;
}
else
{
lean_dec(v___x_2466_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2542_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2470_; uint8_t v___x_2471_; lean_object* v___x_2472_; uint8_t v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2470_ = lean_unsigned_to_nat(10u);
v___x_2471_ = 0;
v___x_2472_ = lean_unsigned_to_nat(100000u);
v___x_2473_ = 0;
v___x_2474_ = lean_unsigned_to_nat(64u);
v___x_2475_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v___x_2475_, 0, v___x_2470_);
lean_ctor_set(v___x_2475_, 1, v___x_2472_);
lean_ctor_set(v___x_2475_, 2, v___x_2474_);
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*3, v___x_2446_);
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*3 + 1, v___x_2446_);
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*3 + 2, v___x_2471_);
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*3 + 3, v___x_2446_);
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*3 + 4, v___x_2446_);
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*3 + 5, v___x_2446_);
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*3 + 6, v___x_2446_);
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*3 + 7, v___x_2446_);
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*3 + 8, v___x_2471_);
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*3 + 9, v___x_2471_);
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*3 + 10, v___x_2473_);
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*3 + 11, v___x_2471_);
v___x_2476_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_2444_, v___x_2475_, v___x_2446_, v___y_2452_, v___y_2458_, v___y_2459_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; lean_object* v___x_2478_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2477_);
lean_dec_ref_known(v___x_2476_, 1);
v___x_2478_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_2451_, v_a_2477_, v___y_2458_, v___y_2459_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_a_2479_);
lean_dec_ref_known(v___x_2478_, 1);
v___x_2480_ = l_Lean_TSyntax_getString(v_path_2461_);
lean_dec(v_path_2461_);
v___x_2481_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v___x_2480_, v_a_2477_, v_a_2479_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_a_2482_; lean_object* v___x_2483_; 
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_a_2482_);
lean_dec_ref_known(v___x_2481_, 1);
v___x_2483_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2453_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2484_);
lean_dec_ref_known(v___x_2483_, 1);
v___x_2485_ = lean_unsigned_to_nat(9u);
v___x_2486_ = lean_unsigned_to_nat(5u);
v___x_2487_ = lean_unsigned_to_nat(8u);
v___x_2488_ = lean_unsigned_to_nat(1000u);
v___x_2489_ = lean_unsigned_to_nat(1024u);
v___x_2490_ = lean_unsigned_to_nat(10000u);
v___x_2491_ = lean_unsigned_to_nat(1048576u);
v___x_2492_ = lean_unsigned_to_nat(50u);
v___x_2493_ = lean_box(0);
v___x_2494_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_2494_, 0, v___x_2485_);
lean_ctor_set(v___x_2494_, 1, v___x_2486_);
lean_ctor_set(v___x_2494_, 2, v___x_2487_);
lean_ctor_set(v___x_2494_, 3, v___x_2487_);
lean_ctor_set(v___x_2494_, 4, v___x_2488_);
lean_ctor_set(v___x_2494_, 5, v___x_2488_);
lean_ctor_set(v___x_2494_, 6, v___x_2472_);
lean_ctor_set(v___x_2494_, 7, v___x_2489_);
lean_ctor_set(v___x_2494_, 8, v___x_2490_);
lean_ctor_set(v___x_2494_, 9, v___x_2488_);
lean_ctor_set(v___x_2494_, 10, v___x_2491_);
lean_ctor_set(v___x_2494_, 11, v___x_2470_);
lean_ctor_set(v___x_2494_, 12, v___x_2492_);
lean_ctor_set(v___x_2494_, 13, v___x_2493_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14, v___x_2471_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 1, v___x_2471_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 2, v___x_2471_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 3, v___x_2471_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 4, v___x_2471_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 5, v___x_2446_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 6, v___x_2446_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 7, v___x_2446_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 8, v___x_2471_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 9, v___x_2471_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 10, v___x_2446_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 11, v___x_2471_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 12, v___x_2446_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 13, v___x_2446_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 14, v___x_2446_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 15, v___x_2446_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 16, v___x_2446_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 17, v___x_2471_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 18, v___x_2446_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 19, v___x_2446_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 20, v___x_2446_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 21, v___x_2446_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 22, v___x_2446_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 23, v___x_2446_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 24, v___x_2446_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 25, v___x_2446_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 26, v___x_2446_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 27, v___x_2446_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 28, v___x_2446_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 29, v___x_2446_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 30, v___x_2471_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 31, v___x_2446_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 32, v___x_2446_);
v___x_2495_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_2494_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; lean_object* v___x_2498_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2496_);
lean_dec_ref_known(v___x_2495_, 1);
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 0, v_a_2484_);
v___x_2498_ = v___x_2468_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2484_);
v___x_2498_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2499_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed), 13, 3);
lean_closure_set(v___x_2499_, 0, v___x_2498_);
lean_closure_set(v___x_2499_, 1, v_a_2482_);
lean_closure_set(v___x_2499_, 2, v___f_2465_);
v___x_2500_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___x_2499_, v_a_2496_, v___x_2493_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
return v___x_2500_;
}
}
else
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2509_; 
lean_dec(v_a_2484_);
lean_dec(v_a_2482_);
lean_del_object(v___x_2468_);
lean_dec_ref(v___f_2465_);
v_a_2502_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2504_ = v___x_2495_;
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2495_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2502_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
}
else
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
lean_dec(v_a_2482_);
lean_del_object(v___x_2468_);
lean_dec_ref(v___f_2465_);
v_a_2510_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2512_ = v___x_2483_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2483_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2510_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_del_object(v___x_2468_);
lean_dec_ref(v___f_2465_);
v_a_2518_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2481_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2481_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_dec(v_a_2477_);
lean_del_object(v___x_2468_);
lean_dec_ref(v___f_2465_);
lean_dec(v_path_2461_);
v_a_2526_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2478_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2478_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
lean_del_object(v___x_2468_);
lean_dec_ref(v___f_2465_);
lean_dec(v_path_2461_);
lean_dec(v_typesStx_2451_);
v_a_2534_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2476_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2476_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
}
else
{
lean_dec_ref(v___f_2465_);
lean_dec(v_path_2461_);
lean_dec(v_typesStx_2451_);
lean_dec(v___x_2444_);
return v___x_2466_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2427_ = stack[0].m_obj;
lean_object* v_a_2428_ = stack[1].m_obj;
lean_object* v_a_2429_ = stack[2].m_obj;
lean_object* v_a_2430_ = stack[3].m_obj;
lean_object* v_a_2431_ = stack[4].m_obj;
lean_object* v_a_2432_ = stack[5].m_obj;
lean_object* v_a_2433_ = stack[6].m_obj;
lean_object* v_a_2434_ = stack[7].m_obj;
lean_object* v_a_2435_ = stack[8].m_obj;
lean_object* v_res_2556_;
v_res_2556_ = l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic(v_x_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
stack->m_obj
 = v_res_2556_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___boxed(lean_object* v_x_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic(v_x_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_);
lean_dec(v_a_2565_);
lean_dec_ref(v_a_2564_);
lean_dec(v_a_2563_);
lean_dec_ref(v_a_2562_);
lean_dec(v_a_2561_);
lean_dec_ref(v_a_2560_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
return v_res_2567_;
}
}
lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1(){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2576_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2577_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0));
v___x_2578_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___closed__1));
v___x_2579_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___boxed), 10, 0);
v___x_2580_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2576_, v___x_2577_, v___x_2578_, v___x_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2581_;
v_res_2581_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1();
stack->m_obj
 = v_res_2581_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___boxed(lean_object* v_a_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1();
return v_res_2583_;
}
}
lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0(lean_object* v___x_2584_, uint8_t v___x_2585_, lean_object* v___x_2586_, lean_object* v___x_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2598_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1);
v___x_2599_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4);
v___x_2600_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5));
v___x_2601_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2601_, 0, v___x_2598_);
lean_ctor_set(v___x_2601_, 1, v___x_2599_);
lean_ctor_set(v___x_2601_, 2, v___x_2584_);
lean_ctor_set(v___x_2601_, 3, v___x_2600_);
lean_ctor_set_uint8(v___x_2601_, sizeof(void*)*4, v___x_2585_);
v___x_2602_ = lean_st_mk_ref(v___x_2601_);
v___x_2603_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_2586_, v___x_2587_, v___x_2602_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2613_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2606_ = v___x_2603_;
v_isShared_2607_ = v_isSharedCheck_2613_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2603_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2613_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2611_; 
v___x_2608_ = lean_st_ref_get(v___x_2602_);
lean_dec(v___x_2602_);
v___x_2609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2609_, 0, v_a_2604_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 0, v___x_2609_);
v___x_2611_ = v___x_2606_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2609_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_dec(v___x_2602_);
v_a_2614_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2603_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2603_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2584_ = stack[0].m_obj;
uint8_t v___x_2585_ = stack[1].m_num;
lean_object* v___x_2586_ = stack[2].m_obj;
lean_object* v___x_2587_ = stack[3].m_obj;
lean_object* v___y_2588_ = stack[4].m_obj;
lean_object* v___y_2589_ = stack[5].m_obj;
lean_object* v___y_2590_ = stack[6].m_obj;
lean_object* v___y_2591_ = stack[7].m_obj;
lean_object* v___y_2592_ = stack[8].m_obj;
lean_object* v___y_2593_ = stack[9].m_obj;
lean_object* v___y_2594_ = stack[10].m_obj;
lean_object* v___y_2595_ = stack[11].m_obj;
lean_object* v___y_2596_ = stack[12].m_obj;
lean_object* v_res_2622_;
v_res_2622_ = l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0(v___x_2584_, v___x_2585_, v___x_2586_, v___x_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
stack->m_obj
 = v_res_2622_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0___boxed(lean_object* v___x_2623_, lean_object* v___x_2624_, lean_object* v___x_2625_, lean_object* v___x_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
uint8_t v___x_3490__boxed_2637_; lean_object* v_res_2638_; 
v___x_3490__boxed_2637_ = lean_unbox(v___x_2624_);
v_res_2638_ = l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0(v___x_2623_, v___x_3490__boxed_2637_, v___x_2625_, v___x_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___x_2626_);
lean_dec(v___x_2625_);
return v_res_2638_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_2639_, lean_object* v_i_2640_, lean_object* v_k_2641_){
_start:
{
lean_object* v___x_2642_; uint8_t v___x_2643_; 
v___x_2642_ = lean_array_get_size(v_keys_2639_);
v___x_2643_ = lean_nat_dec_lt(v_i_2640_, v___x_2642_);
if (v___x_2643_ == 0)
{
lean_dec(v_i_2640_);
return v___x_2643_;
}
else
{
lean_object* v_k_x27_2644_; uint8_t v___x_2645_; 
v_k_x27_2644_ = lean_array_fget_borrowed(v_keys_2639_, v_i_2640_);
v___x_2645_ = l_Lean_instBEqMVarId_beq(v_k_2641_, v_k_x27_2644_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2646_ = lean_unsigned_to_nat(1u);
v___x_2647_ = lean_nat_add(v_i_2640_, v___x_2646_);
lean_dec(v_i_2640_);
v_i_2640_ = v___x_2647_;
goto _start;
}
else
{
lean_dec(v_i_2640_);
return v___x_2643_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2639_ = stack[0].m_obj;
lean_object* v_i_2640_ = stack[1].m_obj;
lean_object* v_k_2641_ = stack[2].m_obj;
uint8_t v_res_2649_;
v_res_2649_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2639_, v_i_2640_, v_k_2641_);
stack->m_num = v_res_2649_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_2650_, lean_object* v_i_2651_, lean_object* v_k_2652_){
_start:
{
uint8_t v_res_2653_; lean_object* v_r_2654_; 
v_res_2653_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2650_, v_i_2651_, v_k_2652_);
lean_dec(v_k_2652_);
lean_dec_ref(v_keys_2650_);
v_r_2654_ = lean_box(v_res_2653_);
return v_r_2654_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2655_, size_t v_x_2656_, lean_object* v_x_2657_){
_start:
{
if (lean_obj_tag(v_x_2655_) == 0)
{
lean_object* v_es_2658_; lean_object* v___x_2659_; size_t v___x_2660_; size_t v___x_2661_; lean_object* v_j_2662_; lean_object* v___x_2663_; 
v_es_2658_ = lean_ctor_get(v_x_2655_, 0);
v___x_2659_ = lean_box(2);
v___x_2660_ = ((size_t)31ULL);
v___x_2661_ = lean_usize_land(v_x_2656_, v___x_2660_);
v_j_2662_ = lean_usize_to_nat(v___x_2661_);
v___x_2663_ = lean_array_get_borrowed(v___x_2659_, v_es_2658_, v_j_2662_);
lean_dec(v_j_2662_);
switch(lean_obj_tag(v___x_2663_))
{
case 0:
{
lean_object* v_key_2664_; uint8_t v___x_2665_; 
v_key_2664_ = lean_ctor_get(v___x_2663_, 0);
v___x_2665_ = l_Lean_instBEqMVarId_beq(v_x_2657_, v_key_2664_);
return v___x_2665_;
}
case 1:
{
lean_object* v_node_2666_; size_t v___x_2667_; size_t v___x_2668_; 
v_node_2666_ = lean_ctor_get(v___x_2663_, 0);
v___x_2667_ = ((size_t)5ULL);
v___x_2668_ = lean_usize_shift_right(v_x_2656_, v___x_2667_);
v_x_2655_ = v_node_2666_;
v_x_2656_ = v___x_2668_;
goto _start;
}
default: 
{
uint8_t v___x_2670_; 
v___x_2670_ = 0;
return v___x_2670_;
}
}
}
else
{
lean_object* v_ks_2671_; lean_object* v___x_2672_; uint8_t v___x_2673_; 
v_ks_2671_ = lean_ctor_get(v_x_2655_, 0);
v___x_2672_ = lean_unsigned_to_nat(0u);
v___x_2673_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_2671_, v___x_2672_, v_x_2657_);
return v___x_2673_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2655_ = stack[0].m_obj;
size_t v_x_2656_ = stack[1].m_num;
lean_object* v_x_2657_ = stack[2].m_obj;
uint8_t v_res_2674_;
v_res_2674_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_2655_, v_x_2656_, v_x_2657_);
stack->m_num = v_res_2674_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2675_, lean_object* v_x_2676_, lean_object* v_x_2677_){
_start:
{
size_t v_x_3657__boxed_2678_; uint8_t v_res_2679_; lean_object* v_r_2680_; 
v_x_3657__boxed_2678_ = lean_unbox_usize(v_x_2676_);
lean_dec(v_x_2676_);
v_res_2679_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_2675_, v_x_3657__boxed_2678_, v_x_2677_);
lean_dec(v_x_2677_);
lean_dec_ref(v_x_2675_);
v_r_2680_ = lean_box(v_res_2679_);
return v_r_2680_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(lean_object* v_x_2681_, lean_object* v_x_2682_){
_start:
{
uint64_t v___x_2683_; size_t v___x_2684_; uint8_t v___x_2685_; 
v___x_2683_ = l_Lean_instHashableMVarId_hash(v_x_2682_);
v___x_2684_ = lean_uint64_to_usize(v___x_2683_);
v___x_2685_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_2681_, v___x_2684_, v_x_2682_);
return v___x_2685_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2681_ = stack[0].m_obj;
lean_object* v_x_2682_ = stack[1].m_obj;
uint8_t v_res_2686_;
v_res_2686_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(v_x_2681_, v_x_2682_);
stack->m_num = v_res_2686_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_2687_, lean_object* v_x_2688_){
_start:
{
uint8_t v_res_2689_; lean_object* v_r_2690_; 
v_res_2689_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(v_x_2687_, v_x_2688_);
lean_dec(v_x_2688_);
lean_dec_ref(v_x_2687_);
v_r_2690_ = lean_box(v_res_2689_);
return v_r_2690_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(lean_object* v_mvarId_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v___x_2694_; lean_object* v_mctx_2695_; lean_object* v_eAssignment_2696_; uint8_t v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2694_ = lean_st_ref_get(v___y_2692_);
v_mctx_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc_ref(v_mctx_2695_);
lean_dec(v___x_2694_);
v_eAssignment_2696_ = lean_ctor_get(v_mctx_2695_, 8);
lean_inc_ref(v_eAssignment_2696_);
lean_dec_ref(v_mctx_2695_);
v___x_2697_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(v_eAssignment_2696_, v_mvarId_2691_);
lean_dec_ref(v_eAssignment_2696_);
v___x_2698_ = lean_box(v___x_2697_);
v___x_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
return v___x_2699_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2691_ = stack[0].m_obj;
lean_object* v___y_2692_ = stack[1].m_obj;
lean_object* v_res_2700_;
v_res_2700_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(v_mvarId_2691_, v___y_2692_);
stack->m_obj
 = v_res_2700_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg___boxed(lean_object* v_mvarId_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(v_mvarId_2701_, v___y_2702_);
lean_dec(v___y_2702_);
lean_dec(v_mvarId_2701_);
return v_res_2704_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1(size_t v_sz_2705_, size_t v_i_2706_, lean_object* v_bs_2707_){
_start:
{
uint8_t v___x_2708_; 
v___x_2708_ = lean_usize_dec_lt(v_i_2706_, v_sz_2705_);
if (v___x_2708_ == 0)
{
return v_bs_2707_;
}
else
{
lean_object* v_v_2709_; lean_object* v_name_2710_; lean_object* v_type_2711_; lean_object* v_value_2712_; lean_object* v___x_2713_; lean_object* v_bs_x27_2714_; uint8_t v___x_2715_; uint8_t v___x_2716_; lean_object* v___x_2717_; size_t v___x_2718_; size_t v___x_2719_; lean_object* v___x_2720_; 
v_v_2709_ = lean_array_uget_borrowed(v_bs_2707_, v_i_2706_);
v_name_2710_ = lean_ctor_get(v_v_2709_, 0);
lean_inc(v_name_2710_);
v_type_2711_ = lean_ctor_get(v_v_2709_, 1);
lean_inc_ref(v_type_2711_);
v_value_2712_ = lean_ctor_get(v_v_2709_, 2);
lean_inc_ref(v_value_2712_);
v___x_2713_ = lean_unsigned_to_nat(0u);
v_bs_x27_2714_ = lean_array_uset(v_bs_2707_, v_i_2706_, v___x_2713_);
v___x_2715_ = 0;
v___x_2716_ = 0;
v___x_2717_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2717_, 0, v_name_2710_);
lean_ctor_set(v___x_2717_, 1, v_type_2711_);
lean_ctor_set(v___x_2717_, 2, v_value_2712_);
lean_ctor_set_uint8(v___x_2717_, sizeof(void*)*3, v___x_2715_);
lean_ctor_set_uint8(v___x_2717_, sizeof(void*)*3 + 1, v___x_2716_);
v___x_2718_ = ((size_t)1ULL);
v___x_2719_ = lean_usize_add(v_i_2706_, v___x_2718_);
v___x_2720_ = lean_array_uset(v_bs_x27_2714_, v_i_2706_, v___x_2717_);
v_i_2706_ = v___x_2719_;
v_bs_2707_ = v___x_2720_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2705_ = stack[0].m_num;
size_t v_i_2706_ = stack[1].m_num;
lean_object* v_bs_2707_ = stack[2].m_obj;
lean_object* v_res_2722_;
v_res_2722_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1(v_sz_2705_, v_i_2706_, v_bs_2707_);
stack->m_obj
 = v_res_2722_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1___boxed(lean_object* v_sz_2723_, lean_object* v_i_2724_, lean_object* v_bs_2725_){
_start:
{
size_t v_sz_boxed_2726_; size_t v_i_boxed_2727_; lean_object* v_res_2728_; 
v_sz_boxed_2726_ = lean_unbox_usize(v_sz_2723_);
lean_dec(v_sz_2723_);
v_i_boxed_2727_ = lean_unbox_usize(v_i_2724_);
lean_dec(v_i_2724_);
v_res_2728_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1(v_sz_boxed_2726_, v_i_boxed_2727_, v_bs_2725_);
return v_res_2728_;
}
}
lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize(lean_object* v_x_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_){
_start:
{
lean_object* v___x_2744_; uint8_t v___x_2745_; 
v___x_2744_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0));
lean_inc(v_x_2734_);
v___x_2745_ = l_Lean_Syntax_isOfKind(v_x_2734_, v___x_2744_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2746_; 
lean_dec(v_x_2734_);
v___x_2746_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2746_;
}
else
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; uint8_t v___x_2750_; lean_object* v_types_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; 
v___x_2747_ = lean_unsigned_to_nat(1u);
v___x_2748_ = l_Lean_Syntax_getArg(v_x_2734_, v___x_2747_);
v___x_2749_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_2748_);
v___x_2750_ = l_Lean_Syntax_isOfKind(v___x_2748_, v___x_2749_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2873_; 
lean_dec(v___x_2748_);
lean_dec(v_x_2734_);
v___x_2873_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2873_;
}
else
{
lean_object* v___x_2874_; lean_object* v___x_2875_; uint8_t v___x_2876_; 
v___x_2874_ = lean_unsigned_to_nat(2u);
v___x_2875_ = l_Lean_Syntax_getArg(v_x_2734_, v___x_2874_);
lean_dec(v_x_2734_);
v___x_2876_ = l_Lean_Syntax_isNone(v___x_2875_);
if (v___x_2876_ == 0)
{
uint8_t v___x_2877_; 
lean_inc(v___x_2875_);
v___x_2877_ = l_Lean_Syntax_matchesNull(v___x_2875_, v___x_2747_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; 
lean_dec(v___x_2875_);
lean_dec(v___x_2748_);
v___x_2878_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2878_;
}
else
{
lean_object* v___x_2879_; lean_object* v_types_2880_; 
v___x_2879_ = lean_unsigned_to_nat(0u);
v_types_2880_ = l_Lean_Syntax_getArg(v___x_2875_, v___x_2879_);
lean_dec(v___x_2875_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2883_; uint8_t v___x_2884_; 
v___x_2883_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_types_2880_);
v___x_2884_ = l_Lean_Syntax_isOfKind(v_types_2880_, v___x_2883_);
if (v___x_2884_ == 0)
{
lean_object* v___x_2885_; 
lean_dec(v_types_2880_);
lean_dec(v___x_2748_);
v___x_2885_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2885_;
}
else
{
goto v___jp_2881_;
}
}
else
{
goto v___jp_2881_;
}
v___jp_2881_:
{
lean_object* v___x_2882_; 
v___x_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2882_, 0, v_types_2880_);
v_types_2752_ = v___x_2882_;
v___y_2753_ = v_a_2735_;
v___y_2754_ = v_a_2736_;
v___y_2755_ = v_a_2737_;
v___y_2756_ = v_a_2738_;
v___y_2757_ = v_a_2739_;
v___y_2758_ = v_a_2740_;
v___y_2759_ = v_a_2741_;
v___y_2760_ = v_a_2742_;
goto v___jp_2751_;
}
}
}
else
{
lean_object* v___x_2886_; 
lean_dec(v___x_2875_);
v___x_2886_ = lean_box(0);
v_types_2752_ = v___x_2886_;
v___y_2753_ = v_a_2735_;
v___y_2754_ = v_a_2736_;
v___y_2755_ = v_a_2737_;
v___y_2756_ = v_a_2738_;
v___y_2757_ = v_a_2739_;
v___y_2758_ = v_a_2740_;
v___y_2759_ = v_a_2741_;
v___y_2760_ = v_a_2742_;
goto v___jp_2751_;
}
}
v___jp_2751_:
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2871_; 
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2871_ == 0)
{
lean_object* v_unused_2872_; 
v_unused_2872_ = lean_ctor_get(v___x_2761_, 0);
lean_dec(v_unused_2872_);
v___x_2763_ = v___x_2761_;
v_isShared_2764_ = v_isSharedCheck_2871_;
goto v_resetjp_2762_;
}
else
{
lean_dec(v___x_2761_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2871_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2765_; uint8_t v___x_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2765_ = lean_unsigned_to_nat(10u);
v___x_2766_ = 0;
v___x_2767_ = lean_unsigned_to_nat(100000u);
v___x_2768_ = 0;
v___x_2769_ = lean_unsigned_to_nat(64u);
v___x_2770_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v___x_2770_, 0, v___x_2765_);
lean_ctor_set(v___x_2770_, 1, v___x_2767_);
lean_ctor_set(v___x_2770_, 2, v___x_2769_);
lean_ctor_set_uint8(v___x_2770_, sizeof(void*)*3, v___x_2750_);
lean_ctor_set_uint8(v___x_2770_, sizeof(void*)*3 + 1, v___x_2750_);
lean_ctor_set_uint8(v___x_2770_, sizeof(void*)*3 + 2, v___x_2766_);
lean_ctor_set_uint8(v___x_2770_, sizeof(void*)*3 + 3, v___x_2750_);
lean_ctor_set_uint8(v___x_2770_, sizeof(void*)*3 + 4, v___x_2750_);
lean_ctor_set_uint8(v___x_2770_, sizeof(void*)*3 + 5, v___x_2750_);
lean_ctor_set_uint8(v___x_2770_, sizeof(void*)*3 + 6, v___x_2750_);
lean_ctor_set_uint8(v___x_2770_, sizeof(void*)*3 + 7, v___x_2750_);
lean_ctor_set_uint8(v___x_2770_, sizeof(void*)*3 + 8, v___x_2766_);
lean_ctor_set_uint8(v___x_2770_, sizeof(void*)*3 + 9, v___x_2766_);
lean_ctor_set_uint8(v___x_2770_, sizeof(void*)*3 + 10, v___x_2768_);
lean_ctor_set_uint8(v___x_2770_, sizeof(void*)*3 + 11, v___x_2766_);
v___x_2771_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_2748_, v___x_2770_, v___x_2750_, v___y_2753_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2773_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v___x_2771_, 1);
v___x_2773_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_types_2752_, v_a_2772_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2775_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec_ref_known(v___x_2773_, 1);
v___x_2775_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2754_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2776_);
lean_dec_ref_known(v___x_2775_, 1);
v___x_2777_ = lean_unsigned_to_nat(9u);
v___x_2778_ = lean_unsigned_to_nat(5u);
v___x_2779_ = lean_unsigned_to_nat(8u);
v___x_2780_ = lean_unsigned_to_nat(1000u);
v___x_2781_ = lean_unsigned_to_nat(1024u);
v___x_2782_ = lean_unsigned_to_nat(10000u);
v___x_2783_ = lean_unsigned_to_nat(1048576u);
v___x_2784_ = lean_unsigned_to_nat(50u);
v___x_2785_ = lean_box(0);
v___x_2786_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_2786_, 0, v___x_2777_);
lean_ctor_set(v___x_2786_, 1, v___x_2778_);
lean_ctor_set(v___x_2786_, 2, v___x_2779_);
lean_ctor_set(v___x_2786_, 3, v___x_2779_);
lean_ctor_set(v___x_2786_, 4, v___x_2780_);
lean_ctor_set(v___x_2786_, 5, v___x_2780_);
lean_ctor_set(v___x_2786_, 6, v___x_2767_);
lean_ctor_set(v___x_2786_, 7, v___x_2781_);
lean_ctor_set(v___x_2786_, 8, v___x_2782_);
lean_ctor_set(v___x_2786_, 9, v___x_2780_);
lean_ctor_set(v___x_2786_, 10, v___x_2783_);
lean_ctor_set(v___x_2786_, 11, v___x_2765_);
lean_ctor_set(v___x_2786_, 12, v___x_2784_);
lean_ctor_set(v___x_2786_, 13, v___x_2785_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14, v___x_2766_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 1, v___x_2766_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 2, v___x_2766_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 3, v___x_2766_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 4, v___x_2766_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 5, v___x_2750_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 6, v___x_2750_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 7, v___x_2750_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 8, v___x_2766_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 9, v___x_2766_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 10, v___x_2750_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 11, v___x_2766_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 12, v___x_2750_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 13, v___x_2750_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 14, v___x_2750_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 15, v___x_2750_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 16, v___x_2750_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 17, v___x_2766_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 18, v___x_2750_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 19, v___x_2750_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 20, v___x_2750_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 21, v___x_2750_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 22, v___x_2750_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 23, v___x_2750_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 24, v___x_2750_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 25, v___x_2750_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 26, v___x_2750_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 27, v___x_2750_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 28, v___x_2750_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 29, v___x_2750_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 30, v___x_2766_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 31, v___x_2750_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*14 + 32, v___x_2750_);
v___x_2787_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_2786_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2790_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2788_);
lean_dec_ref_known(v___x_2787_, 1);
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 0, v_a_2774_);
v___x_2790_ = v___x_2763_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2774_);
v___x_2790_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___f_2794_; lean_object* v___x_2795_; 
v___x_2791_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v___x_2790_, v_a_2772_, v___x_2785_);
v___x_2792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2792_, 0, v_a_2776_);
v___x_2793_ = lean_box(v___x_2766_);
v___f_2794_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0___boxed), 14, 4);
lean_closure_set(v___f_2794_, 0, v___x_2792_);
lean_closure_set(v___f_2794_, 1, v___x_2793_);
lean_closure_set(v___f_2794_, 2, v___x_2785_);
lean_closure_set(v___f_2794_, 3, v___x_2791_);
v___x_2795_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___f_2794_, v_a_2788_, v___x_2785_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v_snd_2797_; lean_object* v_target_2798_; lean_object* v_hypotheses_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v_a_2802_; uint8_t v___x_2803_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2796_);
lean_dec_ref_known(v___x_2795_, 1);
v_snd_2797_ = lean_ctor_get(v_a_2796_, 1);
lean_inc(v_snd_2797_);
lean_dec(v_a_2796_);
v_target_2798_ = lean_ctor_get(v_snd_2797_, 2);
lean_inc_ref(v_target_2798_);
v_hypotheses_2799_ = lean_ctor_get(v_snd_2797_, 3);
lean_inc_ref(v_hypotheses_2799_);
lean_dec(v_snd_2797_);
v___x_2800_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_2798_);
lean_dec_ref(v_target_2798_);
v___x_2801_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(v___x_2800_, v___y_2758_);
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref(v___x_2801_);
v___x_2803_ = lean_unbox(v_a_2802_);
lean_dec(v_a_2802_);
if (v___x_2803_ == 0)
{
size_t v_sz_2804_; size_t v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v_sz_2804_ = lean_array_size(v_hypotheses_2799_);
v___x_2805_ = ((size_t)0ULL);
v___x_2806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1(v_sz_2804_, v___x_2805_, v_hypotheses_2799_);
v___x_2807_ = l_Lean_MVarId_assertHypotheses(v___x_2800_, v___x_2806_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v_snd_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2818_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v_snd_2809_ = lean_ctor_get(v_a_2808_, 1);
v_isSharedCheck_2818_ = !lean_is_exclusive(v_a_2808_);
if (v_isSharedCheck_2818_ == 0)
{
lean_object* v_unused_2819_; 
v_unused_2819_ = lean_ctor_get(v_a_2808_, 0);
lean_dec(v_unused_2819_);
v___x_2811_ = v_a_2808_;
v_isShared_2812_ = v_isSharedCheck_2818_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_snd_2809_);
lean_dec(v_a_2808_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2818_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2813_; lean_object* v___x_2815_; 
v___x_2813_ = lean_box(0);
if (v_isShared_2812_ == 0)
{
lean_ctor_set_tag(v___x_2811_, 1);
lean_ctor_set(v___x_2811_, 1, v___x_2813_);
lean_ctor_set(v___x_2811_, 0, v_snd_2809_);
v___x_2815_ = v___x_2811_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_snd_2809_);
lean_ctor_set(v_reuseFailAlloc_2817_, 1, v___x_2813_);
v___x_2815_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2815_, v___y_2754_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
return v___x_2816_;
}
}
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
v_a_2820_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2807_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2807_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
else
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
lean_dec(v___x_2800_);
lean_dec_ref(v_hypotheses_2799_);
v___x_2828_ = lean_box(0);
v___x_2829_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2828_, v___y_2754_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
return v___x_2829_;
}
}
else
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
v_a_2830_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2795_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2795_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2830_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
}
else
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_dec(v_a_2776_);
lean_dec(v_a_2774_);
lean_dec(v_a_2772_);
lean_del_object(v___x_2763_);
v_a_2839_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2787_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2787_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_dec(v_a_2774_);
lean_dec(v_a_2772_);
lean_del_object(v___x_2763_);
v_a_2847_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2775_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2775_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_dec(v_a_2772_);
lean_del_object(v___x_2763_);
v_a_2855_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2773_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2773_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_del_object(v___x_2763_);
lean_dec(v_types_2752_);
v_a_2863_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2771_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2771_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
}
else
{
lean_dec(v_types_2752_);
lean_dec(v___x_2748_);
return v___x_2761_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_evalBVNormalize_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2734_ = stack[0].m_obj;
lean_object* v_a_2735_ = stack[1].m_obj;
lean_object* v_a_2736_ = stack[2].m_obj;
lean_object* v_a_2737_ = stack[3].m_obj;
lean_object* v_a_2738_ = stack[4].m_obj;
lean_object* v_a_2739_ = stack[5].m_obj;
lean_object* v_a_2740_ = stack[6].m_obj;
lean_object* v_a_2741_ = stack[7].m_obj;
lean_object* v_a_2742_ = stack[8].m_obj;
lean_object* v_res_2887_;
v_res_2887_ = l_Lean_Elab_Tactic_BVDecide_evalBVNormalize(v_x_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_);
stack->m_obj
 = v_res_2887_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___boxed(lean_object* v_x_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l_Lean_Elab_Tactic_BVDecide_evalBVNormalize(v_x_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
lean_dec(v_a_2894_);
lean_dec_ref(v_a_2893_);
lean_dec(v_a_2892_);
lean_dec_ref(v_a_2891_);
lean_dec(v_a_2890_);
lean_dec_ref(v_a_2889_);
return v_res_2898_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0(lean_object* v_mvarId_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
lean_object* v___x_2909_; 
v___x_2909_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(v_mvarId_2899_, v___y_2905_);
return v___x_2909_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2899_ = stack[0].m_obj;
lean_object* v___y_2900_ = stack[1].m_obj;
lean_object* v___y_2901_ = stack[2].m_obj;
lean_object* v___y_2902_ = stack[3].m_obj;
lean_object* v___y_2903_ = stack[4].m_obj;
lean_object* v___y_2904_ = stack[5].m_obj;
lean_object* v___y_2905_ = stack[6].m_obj;
lean_object* v___y_2906_ = stack[7].m_obj;
lean_object* v___y_2907_ = stack[8].m_obj;
lean_object* v_res_2910_;
v_res_2910_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0(v_mvarId_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
stack->m_obj
 = v_res_2910_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___boxed(lean_object* v_mvarId_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0(v_mvarId_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v_mvarId_2911_);
return v_res_2921_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0(lean_object* v_00_u03b2_2922_, lean_object* v_x_2923_, lean_object* v_x_2924_){
_start:
{
uint8_t v___x_2925_; 
v___x_2925_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(v_x_2923_, v_x_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2923_ = stack[1].m_obj;
lean_object* v_x_2924_ = stack[2].m_obj;
uint8_t v_res_2926_;
v_res_2926_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0(lean_box(0), v_x_2923_, v_x_2924_);
stack->m_num = v_res_2926_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2927_, lean_object* v_x_2928_, lean_object* v_x_2929_){
_start:
{
uint8_t v_res_2930_; lean_object* v_r_2931_; 
v_res_2930_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0(v_00_u03b2_2927_, v_x_2928_, v_x_2929_);
lean_dec(v_x_2929_);
lean_dec_ref(v_x_2928_);
v_r_2931_ = lean_box(v_res_2930_);
return v_r_2931_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2932_, lean_object* v_x_2933_, size_t v_x_2934_, lean_object* v_x_2935_){
_start:
{
uint8_t v___x_2936_; 
v___x_2936_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_2933_, v_x_2934_, v_x_2935_);
return v___x_2936_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2933_ = stack[1].m_obj;
size_t v_x_2934_ = stack[2].m_num;
lean_object* v_x_2935_ = stack[3].m_obj;
uint8_t v_res_2937_;
v_res_2937_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1(lean_box(0), v_x_2933_, v_x_2934_, v_x_2935_);
stack->m_num = v_res_2937_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2938_, lean_object* v_x_2939_, lean_object* v_x_2940_, lean_object* v_x_2941_){
_start:
{
size_t v_x_4312__boxed_2942_; uint8_t v_res_2943_; lean_object* v_r_2944_; 
v_x_4312__boxed_2942_ = lean_unbox_usize(v_x_2940_);
lean_dec(v_x_2940_);
v_res_2943_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1(v_00_u03b2_2938_, v_x_2939_, v_x_4312__boxed_2942_, v_x_2941_);
lean_dec(v_x_2941_);
lean_dec_ref(v_x_2939_);
v_r_2944_ = lean_box(v_res_2943_);
return v_r_2944_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2945_, lean_object* v_keys_2946_, lean_object* v_vals_2947_, lean_object* v_heq_2948_, lean_object* v_i_2949_, lean_object* v_k_2950_){
_start:
{
uint8_t v___x_2951_; 
v___x_2951_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2946_, v_i_2949_, v_k_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2946_ = stack[1].m_obj;
lean_object* v_vals_2947_ = stack[2].m_obj;
lean_object* v_i_2949_ = stack[4].m_obj;
lean_object* v_k_2950_ = stack[5].m_obj;
uint8_t v_res_2952_;
v_res_2952_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(lean_box(0), v_keys_2946_, v_vals_2947_, lean_box(0), v_i_2949_, v_k_2950_);
stack->m_num = v_res_2952_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2953_, lean_object* v_keys_2954_, lean_object* v_vals_2955_, lean_object* v_heq_2956_, lean_object* v_i_2957_, lean_object* v_k_2958_){
_start:
{
uint8_t v_res_2959_; lean_object* v_r_2960_; 
v_res_2959_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2953_, v_keys_2954_, v_vals_2955_, v_heq_2956_, v_i_2957_, v_k_2958_);
lean_dec(v_k_2958_);
lean_dec_ref(v_vals_2955_);
lean_dec_ref(v_keys_2954_);
v_r_2960_ = lean_box(v_res_2959_);
return v_r_2960_;
}
}
lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1(){
_start:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2969_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2970_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0));
v___x_2971_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___closed__1));
v___x_2972_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___boxed), 10, 0);
v___x_2973_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2969_, v___x_2970_, v___x_2971_, v___x_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2974_;
v_res_2974_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1();
stack->m_obj
 = v_res_2974_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___boxed(lean_object* v_a_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1();
return v_res_2976_;
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
