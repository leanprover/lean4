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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkDefaultParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(lean_object*, lean_object*);
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
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_24_; lean_object* v_toCold_25_; lean_object* v_env_26_; lean_object* v_options_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_24_ = lean_st_ref_get(v___y_22_);
v_toCold_25_ = lean_ctor_get(v___y_21_, 0);
v_env_26_ = lean_ctor_get(v___x_24_, 0);
lean_inc_ref(v_env_26_);
lean_dec(v___x_24_);
v_options_27_ = lean_ctor_get(v_toCold_25_, 2);
v___x_28_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__2);
v___x_29_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_27_);
v___x_30_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_30_, 0, v_env_26_);
lean_ctor_set(v___x_30_, 1, v___x_28_);
lean_ctor_set(v___x_30_, 2, v___x_29_);
lean_ctor_set(v___x_30_, 3, v_options_27_);
v___x_31_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
lean_ctor_set(v___x_31_, 1, v_msgData_20_);
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___boxed(lean_object* v_msgData_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0(v_msgData_33_, v___y_34_, v___y_35_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg(lean_object* v_msg_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v_ref_42_; lean_object* v___x_43_; lean_object* v_a_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_52_; 
v_ref_42_ = lean_ctor_get(v___y_39_, 2);
v___x_43_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0(v_msg_38_, v___y_39_, v___y_40_);
v_a_44_ = lean_ctor_get(v___x_43_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_52_ == 0)
{
v___x_46_ = v___x_43_;
v_isShared_47_ = v_isSharedCheck_52_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_a_44_);
lean_dec(v___x_43_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_52_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_48_; lean_object* v___x_50_; 
lean_inc(v_ref_42_);
v___x_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_48_, 0, v_ref_42_);
lean_ctor_set(v___x_48_, 1, v_a_44_);
if (v_isShared_47_ == 0)
{
lean_ctor_set_tag(v___x_46_, 1);
lean_ctor_set(v___x_46_, 0, v___x_48_);
v___x_50_ = v___x_46_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v___x_48_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg___boxed(lean_object* v_msg_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg(v_msg_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
return v_res_57_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__5(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__4));
v___x_67_ = l_Lean_stringToMessageData(v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v___x_71_; lean_object* v_env_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_71_ = lean_st_ref_get(v_a_69_);
v_env_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc_ref(v_env_72_);
lean_dec(v___x_71_);
v___x_73_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__3));
v___x_74_ = l_Lean_Environment_getModuleIdx_x3f(v_env_72_, v___x_73_);
lean_dec_ref(v_env_72_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__5, &l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__5);
v___x_76_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg(v___x_75_, v_a_68_, v_a_69_);
return v___x_76_;
}
else
{
lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_84_; 
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_84_ == 0)
{
lean_object* v_unused_85_; 
v_unused_85_ = lean_ctor_get(v___x_74_, 0);
lean_dec(v_unused_85_);
v___x_78_ = v___x_74_;
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
else
{
lean_dec(v___x_74_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_80_ = lean_box(0);
if (v_isShared_79_ == 0)
{
lean_ctor_set_tag(v___x_78_, 0);
lean_ctor_set(v___x_78_, 0, v___x_80_);
v___x_82_ = v___x_78_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_80_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___boxed(lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v_a_86_, v_a_87_);
lean_dec(v_a_87_);
lean_dec_ref(v_a_86_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0(lean_object* v_00_u03b1_90_, lean_object* v_msg_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___redArg(v_msg_91_, v___y_92_, v___y_93_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0___boxed(lean_object* v_00_u03b1_96_, lean_object* v_msg_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0(v_00_u03b1_96_, v_msg_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(lean_object* v_msgData_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v___x_108_; lean_object* v_env_109_; lean_object* v___x_110_; lean_object* v_toCold_111_; lean_object* v_mctx_112_; lean_object* v_lctx_113_; lean_object* v_options_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_108_ = lean_st_ref_get(v___y_106_);
v_env_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc_ref(v_env_109_);
lean_dec(v___x_108_);
v___x_110_ = lean_st_ref_get(v___y_104_);
v_toCold_111_ = lean_ctor_get(v___y_105_, 0);
v_mctx_112_ = lean_ctor_get(v___x_110_, 0);
lean_inc_ref(v_mctx_112_);
lean_dec(v___x_110_);
v_lctx_113_ = lean_ctor_get(v___y_103_, 2);
v_options_114_ = lean_ctor_get(v_toCold_111_, 2);
lean_inc_ref(v_options_114_);
lean_inc_ref(v_lctx_113_);
v___x_115_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_115_, 0, v_env_109_);
lean_ctor_set(v___x_115_, 1, v_mctx_112_);
lean_ctor_set(v___x_115_, 2, v_lctx_113_);
lean_ctor_set(v___x_115_, 3, v_options_114_);
v___x_116_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v_msgData_102_);
v___x_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0___boxed(lean_object* v_msgData_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v_msgData_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
return v_res_124_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_box(1);
v___x_126_ = l_Lean_MessageData_ofFormat(v___x_125_);
return v___x_126_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__2));
v___x_131_ = l_Lean_MessageData_ofFormat(v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3(lean_object* v_x_132_, lean_object* v_x_133_){
_start:
{
if (lean_obj_tag(v_x_133_) == 0)
{
return v_x_132_;
}
else
{
lean_object* v_head_134_; lean_object* v_tail_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_157_; 
v_head_134_ = lean_ctor_get(v_x_133_, 0);
v_tail_135_ = lean_ctor_get(v_x_133_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v_x_133_);
if (v_isSharedCheck_157_ == 0)
{
v___x_137_ = v_x_133_;
v_isShared_138_ = v_isSharedCheck_157_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_tail_135_);
lean_inc(v_head_134_);
lean_dec(v_x_133_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_157_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v_before_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_155_; 
v_before_139_ = lean_ctor_get(v_head_134_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v_head_134_);
if (v_isSharedCheck_155_ == 0)
{
lean_object* v_unused_156_; 
v_unused_156_ = lean_ctor_get(v_head_134_, 1);
lean_dec(v_unused_156_);
v___x_141_ = v_head_134_;
v_isShared_142_ = v_isSharedCheck_155_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_before_139_);
lean_dec(v_head_134_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_155_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_143_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_142_ == 0)
{
lean_ctor_set_tag(v___x_141_, 7);
lean_ctor_set(v___x_141_, 1, v___x_143_);
lean_ctor_set(v___x_141_, 0, v_x_132_);
v___x_145_ = v___x_141_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_x_132_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v___x_143_);
v___x_145_ = v_reuseFailAlloc_154_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v___x_146_; lean_object* v___x_148_; 
v___x_146_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_138_ == 0)
{
lean_ctor_set_tag(v___x_137_, 7);
lean_ctor_set(v___x_137_, 1, v___x_146_);
lean_ctor_set(v___x_137_, 0, v___x_145_);
v___x_148_ = v___x_137_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_145_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v___x_146_);
v___x_148_ = v_reuseFailAlloc_153_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = l_Lean_MessageData_ofSyntax(v_before_139_);
v___x_150_ = l_Lean_indentD(v___x_149_);
v___x_151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_148_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v_x_132_ = v___x_151_;
v_x_133_ = v_tail_135_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(lean_object* v_opts_158_, lean_object* v_opt_159_){
_start:
{
lean_object* v_name_160_; lean_object* v_defValue_161_; lean_object* v_map_162_; lean_object* v___x_163_; 
v_name_160_ = lean_ctor_get(v_opt_159_, 0);
v_defValue_161_ = lean_ctor_get(v_opt_159_, 1);
v_map_162_ = lean_ctor_get(v_opts_158_, 0);
v___x_163_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_162_, v_name_160_);
if (lean_obj_tag(v___x_163_) == 0)
{
uint8_t v___x_164_; 
v___x_164_ = lean_unbox(v_defValue_161_);
return v___x_164_;
}
else
{
lean_object* v_val_165_; 
v_val_165_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_val_165_);
lean_dec_ref_known(v___x_163_, 1);
if (lean_obj_tag(v_val_165_) == 1)
{
uint8_t v_v_166_; 
v_v_166_ = lean_ctor_get_uint8(v_val_165_, 0);
lean_dec_ref_known(v_val_165_, 0);
return v_v_166_;
}
else
{
uint8_t v___x_167_; 
lean_dec(v_val_165_);
v___x_167_ = lean_unbox(v_defValue_161_);
return v___x_167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_168_, lean_object* v_opt_169_){
_start:
{
uint8_t v_res_170_; lean_object* v_r_171_; 
v_res_170_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_opts_168_, v_opt_169_);
lean_dec_ref(v_opt_169_);
lean_dec_ref(v_opts_168_);
v_r_171_ = lean_box(v_res_170_);
return v_r_171_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__1));
v___x_176_ = l_Lean_MessageData_ofFormat(v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(lean_object* v_msgData_177_, lean_object* v_macroStack_178_, lean_object* v___y_179_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_181_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_179_);
v___x_182_ = l_Lean_Elab_pp_macroStack;
v___x_183_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v___x_181_, v___x_182_);
lean_dec_ref(v___x_181_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; 
lean_dec(v_macroStack_178_);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v_msgData_177_);
return v___x_184_;
}
else
{
if (lean_obj_tag(v_macroStack_178_) == 0)
{
lean_object* v___x_185_; 
v___x_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_185_, 0, v_msgData_177_);
return v___x_185_;
}
else
{
lean_object* v_head_186_; lean_object* v_after_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_202_; 
v_head_186_ = lean_ctor_get(v_macroStack_178_, 0);
lean_inc(v_head_186_);
v_after_187_ = lean_ctor_get(v_head_186_, 1);
v_isSharedCheck_202_ = !lean_is_exclusive(v_head_186_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; 
v_unused_203_ = lean_ctor_get(v_head_186_, 0);
lean_dec(v_unused_203_);
v___x_189_ = v_head_186_;
v_isShared_190_ = v_isSharedCheck_202_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_after_187_);
lean_dec(v_head_186_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_202_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_191_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_190_ == 0)
{
lean_ctor_set_tag(v___x_189_, 7);
lean_ctor_set(v___x_189_, 1, v___x_191_);
lean_ctor_set(v___x_189_, 0, v_msgData_177_);
v___x_193_ = v___x_189_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_msgData_177_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v___x_191_);
v___x_193_ = v_reuseFailAlloc_201_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v_msgData_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_194_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2);
v___x_195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_193_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
v___x_196_ = l_Lean_MessageData_ofSyntax(v_after_187_);
v___x_197_ = l_Lean_indentD(v___x_196_);
v_msgData_198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_198_, 0, v___x_195_);
lean_ctor_set(v_msgData_198_, 1, v___x_197_);
v___x_199_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3(v_msgData_198_, v_macroStack_178_);
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
return v___x_200_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_204_, lean_object* v_macroStack_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_msgData_204_, v_macroStack_205_, v___y_206_);
lean_dec_ref(v___y_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(lean_object* v_msg_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_ref_217_; lean_object* v_macroStack_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v_a_221_; lean_object* v___x_222_; lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_231_; 
v_ref_217_ = lean_ctor_get(v___y_214_, 2);
v_macroStack_218_ = lean_ctor_get(v___y_210_, 1);
v___x_219_ = l_Lean_Elab_getBetterRef(v_ref_217_, v_macroStack_218_);
v___x_220_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v_msg_209_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
v_a_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_221_);
lean_dec_ref(v___x_220_);
lean_inc(v_macroStack_218_);
v___x_222_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_a_221_, v_macroStack_218_, v___y_214_);
v_a_223_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_231_ == 0)
{
v___x_225_ = v___x_222_;
v_isShared_226_ = v_isSharedCheck_231_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_222_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_231_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_219_);
lean_ctor_set(v___x_227_, 1, v_a_223_);
if (v_isShared_226_ == 0)
{
lean_ctor_set_tag(v___x_225_, 1);
lean_ctor_set(v___x_225_, 0, v___x_227_);
v___x_229_ = v___x_225_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg___boxed(lean_object* v_msg_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v_msg_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
return v_res_240_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__0));
v___x_243_ = l_Lean_stringToMessageData(v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__2));
v___x_246_ = l_Lean_stringToMessageData(v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_toCold_254_; lean_object* v_fileName_255_; lean_object* v___x_256_; 
v_toCold_254_ = lean_ctor_get(v_a_251_, 0);
v_fileName_255_ = lean_ctor_get(v_toCold_254_, 0);
lean_inc_ref(v_fileName_255_);
v___x_256_ = l_System_FilePath_parent(v_fileName_255_);
if (lean_obj_tag(v___x_256_) == 1)
{
lean_object* v_val_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
v_val_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_val_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
lean_ctor_set_tag(v___x_259_, 0);
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_val_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
lean_dec(v___x_256_);
v___x_265_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1, &l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1);
lean_inc_ref(v_fileName_255_);
v___x_266_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_266_, 0, v_fileName_255_);
v___x_267_ = l_Lean_MessageData_ofFormat(v___x_266_);
v___x_268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_265_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3, &l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3);
v___x_270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_268_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v___x_270_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___boxed(lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_);
lean_dec(v_a_277_);
lean_dec_ref(v_a_276_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
lean_dec(v_a_273_);
lean_dec_ref(v_a_272_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0(lean_object* v_00_u03b1_280_, lean_object* v_msg_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v_msg_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___boxed(lean_object* v_00_u03b1_290_, lean_object* v_msg_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0(v_00_u03b1_290_, v_msg_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1(lean_object* v_msgData_300_, lean_object* v_macroStack_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_msgData_300_, v_macroStack_301_, v___y_306_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___boxed(lean_object* v_msgData_310_, lean_object* v_macroStack_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1(v_msgData_310_, v_macroStack_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(lean_object* v_lratPath_320_, lean_object* v_cfg_321_, lean_object* v_types_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v___x_330_, 1);
v___x_332_ = l_System_FilePath_join(v_a_331_, v_lratPath_320_);
v___x_333_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new(v___x_332_, v_cfg_321_, v_types_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
return v___x_333_;
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
lean_dec(v_types_322_);
lean_dec_ref(v_cfg_321_);
lean_dec_ref(v_lratPath_320_);
v_a_334_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_330_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_330_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext___boxed(lean_object* v_lratPath_342_, lean_object* v_cfg_343_, lean_object* v_types_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v_lratPath_342_, v_cfg_343_, v_types_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0(lean_object* v_g_353_, lean_object* v___x_354_, lean_object* v___x_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(v_g_353_, v___x_354_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; 
v_unused_373_ = lean_ctor_get(v___x_365_, 0);
lean_dec(v_unused_373_);
v___x_367_ = v___x_365_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_dec(v___x_365_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_355_);
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_355_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
v_a_374_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_365_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_365_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0___boxed(lean_object* v_g_382_, lean_object* v___x_383_, lean_object* v___x_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0(v_g_382_, v___x_383_, v___x_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(lean_object* v_g_395_, lean_object* v_hypotheses_396_, lean_object* v_ctx_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___f_407_; lean_object* v___x_408_; 
v___x_405_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed), 9, 1);
lean_closure_set(v___x_405_, 0, v_ctx_397_);
v___x_406_ = lean_box(0);
v___f_407_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0___boxed), 12, 3);
lean_closure_set(v___f_407_, 0, v_g_395_);
lean_closure_set(v___f_407_, 1, v___x_405_);
lean_closure_set(v___f_407_, 2, v___x_406_);
v___x_408_ = l_Lean_Meta_Tactic_BVDecide_M_run___redArg(v___f_407_, v_hypotheses_396_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___boxed(lean_object* v_g_409_, lean_object* v_hypotheses_410_, lean_object* v_ctx_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(v_g_409_, v_hypotheses_410_, v_ctx_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
return v_res_419_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_ensureBvDecide_spec__0_spec__0___closed__0);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0);
v___x_423_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
lean_ctor_set(v___x_423_, 2, v___x_422_);
lean_ctor_set(v___x_423_, 3, v___x_422_);
return v___x_423_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_box(0);
v___x_425_ = lean_unsigned_to_nat(16u);
v___x_426_ = lean_mk_array(v___x_425_, v___x_424_);
return v___x_426_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_427_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2);
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v___x_427_);
return v___x_429_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3);
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
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___y_455_; lean_object* v___x_465_; 
lean_inc_ref(v_ctx_435_);
v___x_447_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_ctx_435_);
v___x_448_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1);
v___x_449_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4);
v___x_450_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5));
v___x_451_ = 0;
v___x_452_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_452_, 0, v___x_448_);
lean_ctor_set(v___x_452_, 1, v___x_449_);
lean_ctor_set(v___x_452_, 2, v_target_434_);
lean_ctor_set(v___x_452_, 3, v___x_450_);
lean_ctor_set_uint8(v___x_452_, sizeof(void*)*4, v___x_451_);
v___x_453_ = lean_st_mk_ref(v___x_452_);
v___x_465_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_447_, v___x_453_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
lean_dec_ref(v___x_447_);
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
lean_object* v___x_468_; lean_object* v_target_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v_hypotheses_472_; lean_object* v___x_473_; 
lean_dec_ref(v_warn_436_);
v___x_468_ = lean_st_ref_get(v___x_453_);
v_target_469_ = lean_ctor_get(v___x_468_, 2);
lean_inc_ref(v_target_469_);
lean_dec(v___x_468_);
v___x_470_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_469_);
lean_dec_ref(v_target_469_);
v___x_471_ = lean_st_ref_get(v___x_453_);
v_hypotheses_472_ = lean_ctor_get(v___x_471_, 3);
lean_inc_ref(v_hypotheses_472_);
lean_dec(v___x_471_);
v___x_473_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(v___x_470_, v_hypotheses_472_, v_ctx_435_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
v___y_455_ = v___x_473_;
goto v___jp_454_;
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
v___y_455_ = v___x_474_;
goto v___jp_454_;
}
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec(v___x_453_);
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
v___jp_454_:
{
if (lean_obj_tag(v___y_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_464_; 
v_a_456_ = lean_ctor_get(v___y_455_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___y_455_);
if (v_isSharedCheck_464_ == 0)
{
v___x_458_ = v___y_455_;
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___y_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_460_ = lean_st_ref_get(v___x_453_);
lean_dec(v___x_453_);
lean_dec(v___x_460_);
if (v_isShared_459_ == 0)
{
v___x_462_ = v___x_458_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_456_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
else
{
lean_dec(v___x_453_);
return v___y_455_;
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
v_ref_499_ = lean_ctor_get(v___y_497_, 2);
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
lean_object* v_toCold_546_; lean_object* v_fileName_547_; lean_object* v_fileMap_548_; lean_object* v___x_549_; 
v_toCold_546_ = lean_ctor_get(v_a_543_, 0);
v_fileName_547_ = lean_ctor_get(v_toCold_546_, 0);
v_fileMap_548_ = lean_ctor_get(v_toCold_546_, 1);
lean_inc_ref(v_fileName_547_);
v___x_549_ = l_System_FilePath_fileName(v_fileName_547_);
if (lean_obj_tag(v___x_549_) == 1)
{
lean_object* v_val_550_; lean_object* v___x_551_; 
v_val_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_val_550_);
lean_dec_ref_known(v___x_549_, 1);
v___x_551_ = l_Lean_Elab_Term_getDeclName_x3f___redArg(v_a_539_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_a_552_);
lean_dec_ref_known(v___x_551_, 1);
if (lean_obj_tag(v_a_552_) == 1)
{
lean_object* v_val_553_; lean_object* v___x_554_; lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_578_; 
v_val_553_ = lean_ctor_get(v_a_552_, 0);
lean_inc(v_val_553_);
lean_dec_ref_known(v_a_552_, 1);
v___x_554_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v_a_543_);
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_578_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_578_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_578_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v_line_560_; lean_object* v_column_561_; lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
lean_inc_ref(v_fileMap_548_);
v___x_559_ = l_Lean_FileMap_toPosition(v_fileMap_548_, v_a_555_);
lean_dec(v_a_555_);
v_line_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_line_560_);
v_column_561_ = lean_ctor_get(v___x_559_, 1);
lean_inc(v_column_561_);
lean_dec_ref(v___x_559_);
v___x_562_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__0));
v___x_563_ = lean_string_append(v_val_550_, v___x_562_);
v___x_564_ = 1;
v___x_565_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_553_, v___x_564_);
v___x_566_ = lean_string_append(v___x_563_, v___x_565_);
lean_dec_ref(v___x_565_);
v___x_567_ = lean_string_append(v___x_566_, v___x_562_);
v___x_568_ = l_Nat_reprFast(v_line_560_);
v___x_569_ = lean_string_append(v___x_567_, v___x_568_);
lean_dec_ref(v___x_568_);
v___x_570_ = lean_string_append(v___x_569_, v___x_562_);
v___x_571_ = l_Nat_reprFast(v_column_561_);
v___x_572_ = lean_string_append(v___x_570_, v___x_571_);
lean_dec_ref(v___x_571_);
v___x_573_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__1));
v___x_574_ = lean_string_append(v___x_572_, v___x_573_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_574_);
v___x_576_ = v___x_557_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec(v_a_552_);
lean_dec(v_val_550_);
v___x_579_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3, &l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3);
v___x_580_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v___x_579_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
return v___x_580_;
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec(v_val_550_);
v_a_581_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_551_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_551_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; 
lean_dec(v___x_549_);
v___x_589_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5, &l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5);
v___x_590_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v___x_589_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
return v___x_590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___boxed(lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(lean_object* v_cfg_599_, lean_object* v_types_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_610_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_a_609_);
lean_dec_ref_known(v___x_608_, 1);
v___x_610_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v_a_609_, v_cfg_599_, v_types_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
return v___x_610_;
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
lean_dec(v_types_600_);
lean_dec_ref(v_cfg_599_);
v_a_611_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_608_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_608_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext___boxed(lean_object* v_cfg_619_, lean_object* v_types_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(v_cfg_619_, v_types_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorIdx(lean_object* v_x_629_){
_start:
{
if (lean_obj_tag(v_x_629_) == 0)
{
lean_object* v___x_630_; 
v___x_630_ = lean_unsigned_to_nat(0u);
return v___x_630_;
}
else
{
lean_object* v___x_631_; 
v___x_631_ = lean_unsigned_to_nat(1u);
return v___x_631_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorIdx___boxed(lean_object* v_x_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorIdx(v_x_632_);
lean_dec(v_x_632_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(lean_object* v_t_634_, lean_object* v_k_635_){
_start:
{
if (lean_obj_tag(v_t_634_) == 0)
{
return v_k_635_;
}
else
{
lean_object* v_path_636_; lean_object* v___x_637_; 
v_path_636_ = lean_ctor_get(v_t_634_, 0);
lean_inc_ref(v_path_636_);
lean_dec_ref_known(v_t_634_, 1);
v___x_637_ = lean_apply_1(v_k_635_, v_path_636_);
return v___x_637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim(lean_object* v_motive_638_, lean_object* v_ctorIdx_639_, lean_object* v_t_640_, lean_object* v_h_641_, lean_object* v_k_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_640_, v_k_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___boxed(lean_object* v_motive_644_, lean_object* v_ctorIdx_645_, lean_object* v_t_646_, lean_object* v_h_647_, lean_object* v_k_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim(v_motive_644_, v_ctorIdx_645_, v_t_646_, v_h_647_, v_k_648_);
lean_dec(v_ctorIdx_645_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_normalize_elim___redArg(lean_object* v_t_650_, lean_object* v_normalize_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_650_, v_normalize_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_normalize_elim(lean_object* v_motive_653_, lean_object* v_t_654_, lean_object* v_h_655_, lean_object* v_normalize_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_654_, v_normalize_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_check_elim___redArg(lean_object* v_t_658_, lean_object* v_check_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_658_, v_check_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_check_elim(lean_object* v_motive_661_, lean_object* v_t_662_, lean_object* v_h_663_, lean_object* v_check_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_662_, v_check_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0(lean_object* v_x_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v___x_677_; 
lean_inc(v___y_671_);
lean_inc_ref(v___y_670_);
lean_inc(v___y_669_);
lean_inc_ref(v___y_668_);
lean_inc(v___y_667_);
v___x_677_ = lean_apply_10(v_x_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, lean_box(0));
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0___boxed(lean_object* v_x_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0(v_x_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(lean_object* v_mvarId_690_, lean_object* v_x_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v___f_702_; lean_object* v___x_703_; 
lean_inc(v___y_696_);
lean_inc_ref(v___y_695_);
lean_inc(v___y_694_);
lean_inc_ref(v___y_693_);
lean_inc(v___y_692_);
v___f_702_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_702_, 0, v_x_691_);
lean_closure_set(v___f_702_, 1, v___y_692_);
lean_closure_set(v___f_702_, 2, v___y_693_);
lean_closure_set(v___f_702_, 3, v___y_694_);
lean_closure_set(v___f_702_, 4, v___y_695_);
lean_closure_set(v___f_702_, 5, v___y_696_);
v___x_703_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_690_, v___f_702_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_703_) == 0)
{
return v___x_703_;
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_703_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_703_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___boxed(lean_object* v_mvarId_712_, lean_object* v_x_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v_mvarId_712_, v_x_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1(lean_object* v_00_u03b1_725_, lean_object* v_mvarId_726_, lean_object* v_x_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v_mvarId_726_, v_x_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___boxed(lean_object* v_00_u03b1_739_, lean_object* v_mvarId_740_, lean_object* v_x_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1(v_00_u03b1_739_, v_mvarId_740_, v_x_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(lean_object* v_e_753_){
_start:
{
if (lean_obj_tag(v_e_753_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_763_; 
v_a_755_ = lean_ctor_get(v_e_753_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v_e_753_);
if (v_isSharedCheck_763_ == 0)
{
v___x_757_ = v_e_753_;
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v_e_753_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_759_ = lean_mk_io_user_error(v_a_755_);
if (v_isShared_758_ == 0)
{
lean_ctor_set_tag(v___x_757_, 1);
lean_ctor_set(v___x_757_, 0, v___x_759_);
v___x_761_ = v___x_757_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
v_a_764_ = lean_ctor_get(v_e_753_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v_e_753_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v_e_753_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v_e_753_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
lean_ctor_set_tag(v___x_766_, 0);
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg___boxed(lean_object* v_e_772_, lean_object* v_a_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v_e_772_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2(lean_object* v_00_u03b1_775_, lean_object* v_e_776_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v_e_776_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___boxed(lean_object* v_00_u03b1_779_, lean_object* v_e_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2(v_00_u03b1_779_, v_e_780_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(lean_object* v_msg_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_ref_789_; lean_object* v___x_790_; lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_799_; 
v_ref_789_ = lean_ctor_get(v___y_786_, 2);
v___x_790_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v_msg_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
v_a_791_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_799_ == 0)
{
v___x_793_ = v___x_790_;
v_isShared_794_ = v_isSharedCheck_799_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_790_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_799_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_797_; 
lean_inc(v_ref_789_);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v_ref_789_);
lean_ctor_set(v___x_795_, 1, v_a_791_);
if (v_isShared_794_ == 0)
{
lean_ctor_set_tag(v___x_793_, 1);
lean_ctor_set(v___x_793_, 0, v___x_795_);
v___x_797_ = v___x_793_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg___boxed(lean_object* v_msg_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(v_msg_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(lean_object* v_target_807_, lean_object* v_ctx_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_exprDef_819_; lean_object* v_certDef_820_; lean_object* v_reflectionDef_821_; lean_object* v_solver_822_; lean_object* v_lratPath_823_; lean_object* v_config_824_; lean_object* v_restrictedTypes_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_949_; 
v_exprDef_819_ = lean_ctor_get(v_ctx_808_, 0);
v_certDef_820_ = lean_ctor_get(v_ctx_808_, 1);
v_reflectionDef_821_ = lean_ctor_get(v_ctx_808_, 2);
v_solver_822_ = lean_ctor_get(v_ctx_808_, 3);
v_lratPath_823_ = lean_ctor_get(v_ctx_808_, 4);
v_config_824_ = lean_ctor_get(v_ctx_808_, 5);
v_restrictedTypes_825_ = lean_ctor_get(v_ctx_808_, 6);
v_isSharedCheck_949_ = !lean_is_exclusive(v_ctx_808_);
if (v_isSharedCheck_949_ == 0)
{
v___x_827_ = v_ctx_808_;
v_isShared_828_ = v_isSharedCheck_949_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_restrictedTypes_825_);
lean_inc(v_config_824_);
lean_inc(v_lratPath_823_);
lean_inc(v_solver_822_);
lean_inc(v_reflectionDef_821_);
lean_inc(v_certDef_820_);
lean_inc(v_exprDef_819_);
lean_dec(v_ctx_808_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_949_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v_timeout_851_; uint8_t v_trimProofs_852_; uint8_t v_binaryProofs_853_; uint8_t v_acNf_854_; uint8_t v_andFlattening_855_; uint8_t v_embeddedConstraintSubst_856_; uint8_t v_structures_857_; uint8_t v_fixedInt_858_; uint8_t v_enums_859_; uint8_t v_graphviz_860_; lean_object* v_maxSteps_861_; uint8_t v_shortCircuit_862_; uint8_t v_solverMode_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_948_; 
v_timeout_851_ = lean_ctor_get(v_config_824_, 0);
v_trimProofs_852_ = lean_ctor_get_uint8(v_config_824_, sizeof(void*)*2);
v_binaryProofs_853_ = lean_ctor_get_uint8(v_config_824_, sizeof(void*)*2 + 1);
v_acNf_854_ = lean_ctor_get_uint8(v_config_824_, sizeof(void*)*2 + 2);
v_andFlattening_855_ = lean_ctor_get_uint8(v_config_824_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_856_ = lean_ctor_get_uint8(v_config_824_, sizeof(void*)*2 + 4);
v_structures_857_ = lean_ctor_get_uint8(v_config_824_, sizeof(void*)*2 + 5);
v_fixedInt_858_ = lean_ctor_get_uint8(v_config_824_, sizeof(void*)*2 + 6);
v_enums_859_ = lean_ctor_get_uint8(v_config_824_, sizeof(void*)*2 + 7);
v_graphviz_860_ = lean_ctor_get_uint8(v_config_824_, sizeof(void*)*2 + 8);
v_maxSteps_861_ = lean_ctor_get(v_config_824_, 1);
v_shortCircuit_862_ = lean_ctor_get_uint8(v_config_824_, sizeof(void*)*2 + 9);
v_solverMode_863_ = lean_ctor_get_uint8(v_config_824_, sizeof(void*)*2 + 10);
v_isSharedCheck_948_ = !lean_is_exclusive(v_config_824_);
if (v_isSharedCheck_948_ == 0)
{
v___x_865_ = v_config_824_;
v_isShared_866_ = v_isSharedCheck_948_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_maxSteps_861_);
lean_inc(v_timeout_851_);
lean_dec(v_config_824_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_948_;
goto v_resetjp_864_;
}
v___jp_829_:
{
lean_object* v___x_839_; 
v___x_839_ = l_System_FilePath_fileName(v_lratPath_823_);
if (lean_obj_tag(v___x_839_) == 1)
{
lean_object* v_val_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_848_; 
v_val_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_848_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_val_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_val_840_);
v___x_845_ = v_reuseFailAlloc_847_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_846_; 
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
return v___x_846_;
}
}
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; 
lean_dec(v___x_839_);
v___x_849_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5, &l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5);
v___x_850_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(v___x_849_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
return v___x_850_;
}
}
v_resetjp_864_:
{
lean_object* v___x_867_; uint8_t v___x_868_; lean_object* v___x_870_; 
v___x_867_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_807_);
v___x_868_ = 0;
if (v_isShared_866_ == 0)
{
v___x_870_ = v___x_865_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_timeout_851_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_maxSteps_861_);
lean_ctor_set_uint8(v_reuseFailAlloc_947_, sizeof(void*)*2 + 1, v_binaryProofs_853_);
lean_ctor_set_uint8(v_reuseFailAlloc_947_, sizeof(void*)*2 + 2, v_acNf_854_);
lean_ctor_set_uint8(v_reuseFailAlloc_947_, sizeof(void*)*2 + 3, v_andFlattening_855_);
lean_ctor_set_uint8(v_reuseFailAlloc_947_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_856_);
lean_ctor_set_uint8(v_reuseFailAlloc_947_, sizeof(void*)*2 + 5, v_structures_857_);
lean_ctor_set_uint8(v_reuseFailAlloc_947_, sizeof(void*)*2 + 6, v_fixedInt_858_);
lean_ctor_set_uint8(v_reuseFailAlloc_947_, sizeof(void*)*2 + 7, v_enums_859_);
lean_ctor_set_uint8(v_reuseFailAlloc_947_, sizeof(void*)*2 + 8, v_graphviz_860_);
lean_ctor_set_uint8(v_reuseFailAlloc_947_, sizeof(void*)*2 + 9, v_shortCircuit_862_);
lean_ctor_set_uint8(v_reuseFailAlloc_947_, sizeof(void*)*2 + 10, v_solverMode_863_);
v___x_870_ = v_reuseFailAlloc_947_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_872_; 
lean_ctor_set_uint8(v___x_870_, sizeof(void*)*2, v___x_868_);
lean_inc_ref(v_lratPath_823_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 5, v___x_870_);
v___x_872_ = v___x_827_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_exprDef_819_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_certDef_820_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_reflectionDef_821_);
lean_ctor_set(v_reuseFailAlloc_946_, 3, v_solver_822_);
lean_ctor_set(v_reuseFailAlloc_946_, 4, v_lratPath_823_);
lean_ctor_set(v_reuseFailAlloc_946_, 5, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_946_, 6, v_restrictedTypes_825_);
v___x_872_ = v_reuseFailAlloc_946_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed), 12, 2);
lean_closure_set(v___x_873_, 0, v_target_807_);
lean_closure_set(v___x_873_, 1, v___x_872_);
v___x_874_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v___x_867_, v___x_873_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_937_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_937_ == 0)
{
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_937_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_937_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
if (lean_obj_tag(v_a_875_) == 0)
{
lean_object* v___x_879_; lean_object* v___x_881_; 
lean_dec_ref(v_lratPath_823_);
v___x_879_ = lean_box(0);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_879_);
v___x_881_ = v___x_877_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
else
{
lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_935_; 
lean_del_object(v___x_877_);
v_isSharedCheck_935_ = !lean_is_exclusive(v_a_875_);
if (v_isSharedCheck_935_ == 0)
{
lean_object* v_unused_936_; 
v_unused_936_ = lean_ctor_get(v_a_875_, 0);
lean_dec(v_unused_936_);
v___x_884_ = v_a_875_;
v_isShared_885_ = v_isSharedCheck_935_;
goto v_resetjp_883_;
}
else
{
lean_dec(v_a_875_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_935_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
if (v_trimProofs_852_ == 0)
{
lean_del_object(v___x_884_);
v___y_830_ = v_a_809_;
v___y_831_ = v_a_810_;
v___y_832_ = v_a_811_;
v___y_833_ = v_a_812_;
v___y_834_ = v_a_813_;
v___y_835_ = v_a_814_;
v___y_836_ = v_a_815_;
v___y_837_ = v_a_816_;
v___y_838_ = v_a_817_;
goto v___jp_829_;
}
else
{
lean_object* v_ref_886_; lean_object* v___x_887_; 
v_ref_886_ = lean_ctor_get(v_a_816_, 2);
v___x_887_ = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(v_lratPath_823_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
lean_dec_ref_known(v___x_887_, 1);
v___x_889_ = l_Lean_Meta_Tactic_BVDecide_LRAT_trim(v_a_888_);
lean_dec(v_a_888_);
v___x_890_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v___x_889_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_892_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref_known(v___x_890_, 1);
v___x_892_ = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(v_lratPath_823_, v_a_891_, v_binaryProofs_853_);
lean_dec(v_a_891_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_dec_ref_known(v___x_892_, 1);
lean_del_object(v___x_884_);
v___y_830_ = v_a_809_;
v___y_831_ = v_a_810_;
v___y_832_ = v_a_811_;
v___y_833_ = v_a_812_;
v___y_834_ = v_a_813_;
v___y_835_ = v_a_814_;
v___y_836_ = v_a_815_;
v___y_837_ = v_a_816_;
v___y_838_ = v_a_817_;
goto v___jp_829_;
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_906_; 
lean_dec_ref(v_lratPath_823_);
v_a_893_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_906_ == 0)
{
v___x_895_ = v___x_892_;
v_isShared_896_ = v_isSharedCheck_906_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_892_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_906_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_897_ = lean_io_error_to_string(v_a_893_);
if (v_isShared_885_ == 0)
{
lean_ctor_set_tag(v___x_884_, 3);
lean_ctor_set(v___x_884_, 0, v___x_897_);
v___x_899_ = v___x_884_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_905_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_900_ = l_Lean_MessageData_ofFormat(v___x_899_);
lean_inc(v_ref_886_);
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v_ref_886_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 0, v___x_901_);
v___x_903_ = v___x_895_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_901_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_920_; 
lean_dec_ref(v_lratPath_823_);
v_a_907_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_920_ == 0)
{
v___x_909_ = v___x_890_;
v_isShared_910_ = v_isSharedCheck_920_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_890_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_920_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_911_ = lean_io_error_to_string(v_a_907_);
if (v_isShared_885_ == 0)
{
lean_ctor_set_tag(v___x_884_, 3);
lean_ctor_set(v___x_884_, 0, v___x_911_);
v___x_913_ = v___x_884_;
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
lean_inc(v_ref_886_);
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v_ref_886_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v___x_915_);
v___x_917_ = v___x_909_;
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
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_934_; 
lean_dec_ref(v_lratPath_823_);
v_a_921_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_934_ == 0)
{
v___x_923_ = v___x_887_;
v_isShared_924_ = v_isSharedCheck_934_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_887_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_934_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_925_ = lean_io_error_to_string(v_a_921_);
if (v_isShared_885_ == 0)
{
lean_ctor_set_tag(v___x_884_, 3);
lean_ctor_set(v___x_884_, 0, v___x_925_);
v___x_927_ = v___x_884_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_925_);
v___x_927_ = v_reuseFailAlloc_933_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_928_ = l_Lean_MessageData_ofFormat(v___x_927_);
lean_inc(v_ref_886_);
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v_ref_886_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_929_);
v___x_931_ = v___x_923_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
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
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
lean_dec_ref(v_lratPath_823_);
v_a_938_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_874_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_874_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___boxed(lean_object* v_target_950_, lean_object* v_ctx_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(v_target_950_, v_ctx_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0(lean_object* v_00_u03b1_963_, lean_object* v_msg_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(v_msg_964_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___boxed(lean_object* v_00_u03b1_976_, lean_object* v_msg_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0(v_00_u03b1_976_, v_msg_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
return v_res_988_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_989_ = lean_box(0);
v___x_990_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set(v___x_991_, 1, v___x_989_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg(){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0);
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___boxed(lean_object* v___y_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0(lean_object* v_00_u03b1_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___boxed(lean_object* v_00_u03b1_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0(v_00_u03b1_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(lean_object* v_snd_1019_, lean_object* v_ref_1020_, lean_object* v_a_x3f_1021_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_io_remove_file(v_snd_1019_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec(v_ref_1020_);
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1043_; 
v_a_1032_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1034_ = v___x_1023_;
v_isShared_1035_ = v_isSharedCheck_1043_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1023_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1043_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1036_ = lean_io_error_to_string(v_a_1032_);
v___x_1037_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
v___x_1038_ = l_Lean_MessageData_ofFormat(v___x_1037_);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v_ref_1020_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v___x_1039_);
v___x_1041_ = v___x_1034_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0___boxed(lean_object* v_snd_1044_, lean_object* v_ref_1045_, lean_object* v_a_x3f_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_1044_, v_ref_1045_, v_a_x3f_1046_);
lean_dec(v_a_x3f_1046_);
lean_dec_ref(v_snd_1044_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(lean_object* v_f_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_ref_1059_; lean_object* v___x_1060_; 
v_ref_1059_ = lean_ctor_get(v___y_1056_, 2);
v___x_1060_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v_fst_1062_; lean_object* v_snd_1063_; lean_object* v_r_1064_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1061_);
lean_dec_ref_known(v___x_1060_, 1);
v_fst_1062_ = lean_ctor_get(v_a_1061_, 0);
lean_inc(v_fst_1062_);
v_snd_1063_ = lean_ctor_get(v_a_1061_, 1);
lean_inc_n(v_snd_1063_, 2);
lean_dec(v_a_1061_);
lean_inc(v___y_1057_);
lean_inc_ref(v___y_1056_);
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
lean_inc(v___y_1051_);
lean_inc_ref(v___y_1050_);
v_r_1064_ = lean_apply_11(v_f_1049_, v_fst_1062_, v_snd_1063_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, lean_box(0));
if (lean_obj_tag(v_r_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1089_; 
v_a_1065_ = lean_ctor_get(v_r_1064_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_r_1064_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1067_ = v_r_1064_;
v_isShared_1068_ = v_isSharedCheck_1089_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v_r_1064_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1089_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
lean_inc(v_a_1065_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set_tag(v___x_1067_, 1);
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1071_; 
lean_inc(v_ref_1059_);
v___x_1071_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_1063_, v_ref_1059_, v___x_1070_);
lean_dec_ref(v___x_1070_);
lean_dec(v_snd_1063_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; 
v_unused_1079_ = lean_ctor_get(v___x_1071_, 0);
lean_dec(v_unused_1079_);
v___x_1073_ = v___x_1071_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_dec(v___x_1071_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v_a_1065_);
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1065_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_dec(v_a_1065_);
v_a_1080_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1071_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1071_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v_a_1090_ = lean_ctor_get(v_r_1064_, 0);
lean_inc(v_a_1090_);
lean_dec_ref_known(v_r_1064_, 1);
v___x_1091_ = lean_box(0);
lean_inc(v_ref_1059_);
v___x_1092_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_1063_, v_ref_1059_, v___x_1091_);
lean_dec(v_snd_1063_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; 
v_unused_1100_ = lean_ctor_get(v___x_1092_, 0);
lean_dec(v_unused_1100_);
v___x_1094_ = v___x_1092_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_dec(v___x_1092_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set_tag(v___x_1094_, 1);
lean_ctor_set(v___x_1094_, 0, v_a_1090_);
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1090_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_dec(v_a_1090_);
v_a_1101_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1092_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1092_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1120_; 
lean_dec_ref(v_f_1049_);
v_a_1109_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1111_ = v___x_1060_;
v_isShared_1112_ = v_isSharedCheck_1120_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1060_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1120_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1113_ = lean_io_error_to_string(v_a_1109_);
v___x_1114_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
v___x_1115_ = l_Lean_MessageData_ofFormat(v___x_1114_);
lean_inc(v_ref_1059_);
v___x_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1116_, 0, v_ref_1059_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1116_);
v___x_1118_ = v___x_1111_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___boxed(lean_object* v_f_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(v_f_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1(lean_object* v_00_u03b1_1132_, lean_object* v_f_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(v_f_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___boxed(lean_object* v_00_u03b1_1144_, lean_object* v_f_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1(v_00_u03b1_1144_, v_f_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0(uint8_t v___x_1156_, uint8_t v___x_1157_, lean_object* v___x_1158_, lean_object* v___x_1159_, lean_object* v_a_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1162_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref_known(v___x_1170_, 1);
v___x_1172_ = lean_unsigned_to_nat(9u);
v___x_1173_ = lean_unsigned_to_nat(5u);
v___x_1174_ = lean_unsigned_to_nat(8u);
v___x_1175_ = lean_unsigned_to_nat(1000u);
v___x_1176_ = lean_unsigned_to_nat(1024u);
v___x_1177_ = lean_unsigned_to_nat(10000u);
v___x_1178_ = lean_unsigned_to_nat(1048576u);
v___x_1179_ = lean_unsigned_to_nat(50u);
v___x_1180_ = lean_box(0);
v___x_1181_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_1181_, 0, v___x_1172_);
lean_ctor_set(v___x_1181_, 1, v___x_1173_);
lean_ctor_set(v___x_1181_, 2, v___x_1174_);
lean_ctor_set(v___x_1181_, 3, v___x_1174_);
lean_ctor_set(v___x_1181_, 4, v___x_1175_);
lean_ctor_set(v___x_1181_, 5, v___x_1175_);
lean_ctor_set(v___x_1181_, 6, v___x_1158_);
lean_ctor_set(v___x_1181_, 7, v___x_1176_);
lean_ctor_set(v___x_1181_, 8, v___x_1177_);
lean_ctor_set(v___x_1181_, 9, v___x_1175_);
lean_ctor_set(v___x_1181_, 10, v___x_1178_);
lean_ctor_set(v___x_1181_, 11, v___x_1159_);
lean_ctor_set(v___x_1181_, 12, v___x_1179_);
lean_ctor_set(v___x_1181_, 13, v___x_1180_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14, v___x_1156_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 1, v___x_1156_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 2, v___x_1156_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 3, v___x_1156_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 4, v___x_1156_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 5, v___x_1157_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 6, v___x_1157_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 7, v___x_1157_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 8, v___x_1156_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 9, v___x_1156_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 10, v___x_1157_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 11, v___x_1156_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 12, v___x_1157_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 13, v___x_1157_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 14, v___x_1157_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 15, v___x_1157_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 16, v___x_1157_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 17, v___x_1156_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 18, v___x_1157_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 19, v___x_1157_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 20, v___x_1157_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 21, v___x_1157_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 22, v___x_1157_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 23, v___x_1157_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 24, v___x_1157_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 25, v___x_1157_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 26, v___x_1157_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 27, v___x_1157_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 28, v___x_1157_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 29, v___x_1157_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 30, v___x_1156_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 31, v___x_1157_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*14 + 32, v___x_1157_);
v___x_1182_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_1181_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1183_);
lean_dec_ref_known(v___x_1182_, 1);
v___x_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1184_, 0, v_a_1171_);
v___x_1185_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed), 12, 2);
lean_closure_set(v___x_1185_, 0, v___x_1184_);
lean_closure_set(v___x_1185_, 1, v_a_1160_);
v___x_1186_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___x_1185_, v_a_1183_, v___x_1180_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_dec_ref_known(v___x_1186_, 1);
v___x_1187_ = lean_box(0);
v___x_1188_ = lean_box(0);
v___x_1189_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1187_, v___y_1162_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1196_ == 0)
{
lean_object* v_unused_1197_; 
v_unused_1197_ = lean_ctor_get(v___x_1189_, 0);
lean_dec(v_unused_1197_);
v___x_1191_ = v___x_1189_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_dec(v___x_1189_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v___x_1188_);
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1188_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
else
{
return v___x_1189_;
}
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
v_a_1198_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1186_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1186_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_dec(v_a_1171_);
lean_dec_ref(v_a_1160_);
v_a_1206_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1182_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1182_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec_ref(v_a_1160_);
lean_dec(v___x_1159_);
lean_dec(v___x_1158_);
v_a_1214_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1170_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1170_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0___boxed(lean_object* v___x_1222_, lean_object* v___x_1223_, lean_object* v___x_1224_, lean_object* v___x_1225_, lean_object* v_a_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
uint8_t v___x_5634__boxed_1236_; uint8_t v___x_5635__boxed_1237_; lean_object* v_res_1238_; 
v___x_5634__boxed_1236_ = lean_unbox(v___x_1222_);
v___x_5635__boxed_1237_ = lean_unbox(v___x_1223_);
v_res_1238_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0(v___x_5634__boxed_1236_, v___x_5635__boxed_1237_, v___x_1224_, v___x_1225_, v_a_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1(lean_object* v_a_1239_, lean_object* v_a_1240_, uint8_t v___x_1241_, uint8_t v___x_1242_, lean_object* v___x_1243_, lean_object* v___x_1244_, lean_object* v_x_1245_, lean_object* v_lratFile_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new(v_lratFile_1246_, v_a_1239_, v_a_1240_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___f_1260_; lean_object* v___x_1261_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___x_1256_, 1);
v___x_1258_ = lean_box(v___x_1241_);
v___x_1259_ = lean_box(v___x_1242_);
v___f_1260_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0___boxed), 14, 5);
lean_closure_set(v___f_1260_, 0, v___x_1258_);
lean_closure_set(v___f_1260_, 1, v___x_1259_);
lean_closure_set(v___f_1260_, 2, v___x_1243_);
lean_closure_set(v___f_1260_, 3, v___x_1244_);
lean_closure_set(v___f_1260_, 4, v_a_1257_);
v___x_1261_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1260_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
return v___x_1261_;
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec(v___x_1244_);
lean_dec(v___x_1243_);
v_a_1262_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1256_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1256_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1___boxed(lean_object** _args){
lean_object* v_a_1270_ = _args[0];
lean_object* v_a_1271_ = _args[1];
lean_object* v___x_1272_ = _args[2];
lean_object* v___x_1273_ = _args[3];
lean_object* v___x_1274_ = _args[4];
lean_object* v___x_1275_ = _args[5];
lean_object* v_x_1276_ = _args[6];
lean_object* v_lratFile_1277_ = _args[7];
lean_object* v___y_1278_ = _args[8];
lean_object* v___y_1279_ = _args[9];
lean_object* v___y_1280_ = _args[10];
lean_object* v___y_1281_ = _args[11];
lean_object* v___y_1282_ = _args[12];
lean_object* v___y_1283_ = _args[13];
lean_object* v___y_1284_ = _args[14];
lean_object* v___y_1285_ = _args[15];
lean_object* v___y_1286_ = _args[16];
_start:
{
uint8_t v___x_5785__boxed_1287_; uint8_t v___x_5786__boxed_1288_; lean_object* v_res_1289_; 
v___x_5785__boxed_1287_ = lean_unbox(v___x_1272_);
v___x_5786__boxed_1288_ = lean_unbox(v___x_1273_);
v_res_1289_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1(v_a_1270_, v_a_1271_, v___x_5785__boxed_1287_, v___x_5786__boxed_1288_, v___x_1274_, v___x_1275_, v_x_1276_, v_lratFile_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v_x_1276_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide(lean_object* v_x_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1320_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3));
lean_inc(v_x_1310_);
v___x_1321_ = l_Lean_Syntax_isOfKind(v_x_1310_, v___x_1320_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; 
lean_dec(v_x_1310_);
v___x_1322_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1322_;
}
else
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; lean_object* v_types_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; 
v___x_1323_ = lean_unsigned_to_nat(1u);
v___x_1324_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1323_);
v___x_1325_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_1324_);
v___x_1326_ = l_Lean_Syntax_isOfKind(v___x_1324_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1367_; 
lean_dec(v___x_1324_);
lean_dec(v_x_1310_);
v___x_1367_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1367_;
}
else
{
lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1368_ = lean_unsigned_to_nat(2u);
v___x_1369_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1368_);
lean_dec(v_x_1310_);
v___x_1370_ = l_Lean_Syntax_isNone(v___x_1369_);
if (v___x_1370_ == 0)
{
uint8_t v___x_1371_; 
lean_inc(v___x_1369_);
v___x_1371_ = l_Lean_Syntax_matchesNull(v___x_1369_, v___x_1323_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; 
lean_dec(v___x_1369_);
lean_dec(v___x_1324_);
v___x_1372_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1372_;
}
else
{
lean_object* v___x_1373_; lean_object* v_types_1374_; 
v___x_1373_ = lean_unsigned_to_nat(0u);
v_types_1374_ = l_Lean_Syntax_getArg(v___x_1369_, v___x_1373_);
lean_dec(v___x_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1377_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_types_1374_);
v___x_1378_ = l_Lean_Syntax_isOfKind(v_types_1374_, v___x_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; 
lean_dec(v_types_1374_);
lean_dec(v___x_1324_);
v___x_1379_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1379_;
}
else
{
goto v___jp_1375_;
}
}
else
{
goto v___jp_1375_;
}
v___jp_1375_:
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1376_, 0, v_types_1374_);
v_types_1328_ = v___x_1376_;
v___y_1329_ = v_a_1311_;
v___y_1330_ = v_a_1312_;
v___y_1331_ = v_a_1313_;
v___y_1332_ = v_a_1314_;
v___y_1333_ = v_a_1315_;
v___y_1334_ = v_a_1316_;
v___y_1335_ = v_a_1317_;
v___y_1336_ = v_a_1318_;
goto v___jp_1327_;
}
}
}
else
{
lean_object* v___x_1380_; 
lean_dec(v___x_1369_);
v___x_1380_ = lean_box(0);
v_types_1328_ = v___x_1380_;
v___y_1329_ = v_a_1311_;
v___y_1330_ = v_a_1312_;
v___y_1331_ = v_a_1313_;
v___y_1332_ = v_a_1314_;
v___y_1333_ = v_a_1315_;
v___y_1334_ = v_a_1316_;
v___y_1335_ = v_a_1317_;
v___y_1336_ = v_a_1318_;
goto v___jp_1327_;
}
}
v___jp_1327_:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v___x_1338_; uint8_t v___x_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_dec_ref_known(v___x_1337_, 1);
v___x_1338_ = lean_unsigned_to_nat(10u);
v___x_1339_ = 0;
v___x_1340_ = lean_unsigned_to_nat(100000u);
v___x_1341_ = 0;
v___x_1342_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_1342_, 0, v___x_1338_);
lean_ctor_set(v___x_1342_, 1, v___x_1340_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*2, v___x_1326_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*2 + 1, v___x_1326_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*2 + 2, v___x_1339_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*2 + 3, v___x_1326_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*2 + 4, v___x_1326_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*2 + 5, v___x_1326_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*2 + 6, v___x_1326_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*2 + 7, v___x_1326_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*2 + 8, v___x_1339_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*2 + 9, v___x_1339_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*2 + 10, v___x_1341_);
v___x_1343_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_1324_, v___x_1342_, v___x_1326_, v___y_1329_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___x_1345_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref_known(v___x_1343_, 1);
v___x_1345_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_types_1328_, v_a_1344_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___f_1349_; lean_object* v___x_1350_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1345_, 1);
v___x_1347_ = lean_box(v___x_1339_);
v___x_1348_ = lean_box(v___x_1326_);
v___f_1349_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1___boxed), 17, 6);
lean_closure_set(v___f_1349_, 0, v_a_1344_);
lean_closure_set(v___f_1349_, 1, v_a_1346_);
lean_closure_set(v___f_1349_, 2, v___x_1347_);
lean_closure_set(v___f_1349_, 3, v___x_1348_);
lean_closure_set(v___f_1349_, 4, v___x_1340_);
lean_closure_set(v___f_1349_, 5, v___x_1338_);
v___x_1350_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(v___f_1349_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
return v___x_1350_;
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec(v_a_1344_);
v_a_1351_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1345_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1345_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_dec(v_types_1328_);
v_a_1359_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1343_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1343_);
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
else
{
lean_dec(v_types_1328_);
lean_dec(v___x_1324_);
return v___x_1337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___boxed(lean_object* v_x_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide(v_x_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_);
lean_dec(v_a_1389_);
lean_dec_ref(v_a_1388_);
lean_dec(v_a_1387_);
lean_dec_ref(v_a_1386_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1(){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1401_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1402_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3));
v___x_1403_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2));
v___x_1404_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___boxed), 10, 0);
v___x_1405_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1401_, v___x_1402_, v___x_1403_, v___x_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___boxed(lean_object* v_a_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1();
return v_res_1407_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Array_mkArray0___redArg();
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0(lean_object* v___x_1420_, lean_object* v_a_1421_, uint8_t v___x_1422_, lean_object* v___x_1423_, lean_object* v___x_1424_, lean_object* v___x_1425_, lean_object* v___x_1426_, lean_object* v_tk_1427_, lean_object* v_typesStx_1428_, lean_object* v___x_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(v___x_1420_, v_a_1421_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___x_1440_, 1);
if (lean_obj_tag(v_a_1441_) == 0)
{
lean_object* v_ref_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___y_1452_; 
v_ref_1442_ = lean_ctor_get(v___y_1437_, 2);
v___x_1443_ = l_Lean_SourceInfo_fromRef(v_ref_1442_, v___x_1422_);
v___x_1444_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__1));
v___x_1445_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__2));
v___x_1446_ = l_Lean_Name_mkStr4(v___x_1423_, v___x_1424_, v___x_1425_, v___x_1445_);
v___x_1447_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3));
lean_inc(v___x_1443_);
v___x_1448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1443_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
v___x_1449_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5));
v___x_1450_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6);
if (lean_obj_tag(v_typesStx_1428_) == 1)
{
lean_object* v_val_1464_; lean_object* v___x_1465_; 
v_val_1464_ = lean_ctor_get(v_typesStx_1428_, 0);
lean_inc(v_val_1464_);
lean_dec_ref_known(v_typesStx_1428_, 1);
v___x_1465_ = l_Array_mkArray1___redArg(v_val_1464_);
v___y_1452_ = v___x_1465_;
goto v___jp_1451_;
}
else
{
lean_object* v___x_1466_; 
lean_dec(v_typesStx_1428_);
v___x_1466_ = lean_mk_empty_array_with_capacity(v___x_1429_);
v___y_1452_ = v___x_1466_;
goto v___jp_1451_;
}
v___jp_1451_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1453_ = l_Array_append___redArg(v___x_1450_, v___y_1452_);
lean_dec_ref(v___y_1452_);
lean_inc(v___x_1443_);
v___x_1454_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1443_);
lean_ctor_set(v___x_1454_, 1, v___x_1449_);
lean_ctor_set(v___x_1454_, 2, v___x_1453_);
v___x_1455_ = l_Lean_Syntax_node3(v___x_1443_, v___x_1446_, v___x_1448_, v___x_1426_, v___x_1454_);
v___x_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1444_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
v___x_1457_ = lean_box(0);
v___x_1458_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1456_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
lean_ctor_set(v___x_1458_, 2, v___x_1457_);
lean_ctor_set(v___x_1458_, 3, v___x_1457_);
lean_ctor_set(v___x_1458_, 4, v___x_1457_);
lean_ctor_set(v___x_1458_, 5, v___x_1457_);
lean_inc(v_ref_1442_);
v___x_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1459_, 0, v_ref_1442_);
v___x_1460_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__7));
v___x_1461_ = 4;
v___x_1462_ = l_Lean_MessageData_nil;
v___x_1463_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1427_, v___x_1458_, v___x_1459_, v___x_1460_, v___x_1457_, v___x_1461_, v___x_1462_, v___y_1437_, v___y_1438_);
return v___x_1463_;
}
}
else
{
lean_object* v_path_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1500_; 
v_path_1467_ = lean_ctor_get(v_a_1441_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_a_1441_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1469_ = v_a_1441_;
v_isShared_1470_ = v_isSharedCheck_1500_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_path_1467_);
lean_dec(v_a_1441_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1500_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v_ref_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___y_1481_; 
v_ref_1471_ = lean_ctor_get(v___y_1437_, 2);
v___x_1472_ = l_Lean_SourceInfo_fromRef(v_ref_1471_, v___x_1422_);
v___x_1473_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__1));
v___x_1474_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__8));
v___x_1475_ = l_Lean_Name_mkStr4(v___x_1423_, v___x_1424_, v___x_1425_, v___x_1474_);
v___x_1476_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__9));
lean_inc(v___x_1472_);
v___x_1477_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1472_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
v___x_1478_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5));
v___x_1479_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6);
if (lean_obj_tag(v_typesStx_1428_) == 1)
{
lean_object* v_val_1497_; lean_object* v___x_1498_; 
v_val_1497_ = lean_ctor_get(v_typesStx_1428_, 0);
lean_inc(v_val_1497_);
lean_dec_ref_known(v_typesStx_1428_, 1);
v___x_1498_ = l_Array_mkArray1___redArg(v_val_1497_);
v___y_1481_ = v___x_1498_;
goto v___jp_1480_;
}
else
{
lean_object* v___x_1499_; 
lean_dec(v_typesStx_1428_);
v___x_1499_ = lean_mk_empty_array_with_capacity(v___x_1429_);
v___y_1481_ = v___x_1499_;
goto v___jp_1480_;
}
v___jp_1480_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1482_ = l_Array_append___redArg(v___x_1479_, v___y_1481_);
lean_dec_ref(v___y_1481_);
lean_inc(v___x_1472_);
v___x_1483_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1472_);
lean_ctor_set(v___x_1483_, 1, v___x_1478_);
lean_ctor_set(v___x_1483_, 2, v___x_1482_);
v___x_1484_ = lean_box(2);
v___x_1485_ = l_Lean_Syntax_mkStrLit(v_path_1467_, v___x_1484_);
v___x_1486_ = l_Lean_Syntax_node4(v___x_1472_, v___x_1475_, v___x_1477_, v___x_1426_, v___x_1483_, v___x_1485_);
v___x_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1473_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = lean_box(0);
v___x_1489_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1487_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
lean_ctor_set(v___x_1489_, 2, v___x_1488_);
lean_ctor_set(v___x_1489_, 3, v___x_1488_);
lean_ctor_set(v___x_1489_, 4, v___x_1488_);
lean_ctor_set(v___x_1489_, 5, v___x_1488_);
lean_inc(v_ref_1471_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 0, v_ref_1471_);
v___x_1491_ = v___x_1469_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_ref_1471_);
v___x_1491_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1492_; uint8_t v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1492_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__7));
v___x_1493_ = 4;
v___x_1494_ = l_Lean_MessageData_nil;
v___x_1495_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1427_, v___x_1489_, v___x_1491_, v___x_1492_, v___x_1488_, v___x_1493_, v___x_1494_, v___y_1437_, v___y_1438_);
return v___x_1495_;
}
}
}
}
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_dec(v_typesStx_1428_);
lean_dec(v_tk_1427_);
lean_dec(v___x_1426_);
lean_dec_ref(v___x_1425_);
lean_dec_ref(v___x_1424_);
lean_dec_ref(v___x_1423_);
v_a_1501_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1440_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1440_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___boxed(lean_object** _args){
lean_object* v___x_1509_ = _args[0];
lean_object* v_a_1510_ = _args[1];
lean_object* v___x_1511_ = _args[2];
lean_object* v___x_1512_ = _args[3];
lean_object* v___x_1513_ = _args[4];
lean_object* v___x_1514_ = _args[5];
lean_object* v___x_1515_ = _args[6];
lean_object* v_tk_1516_ = _args[7];
lean_object* v_typesStx_1517_ = _args[8];
lean_object* v___x_1518_ = _args[9];
lean_object* v___y_1519_ = _args[10];
lean_object* v___y_1520_ = _args[11];
lean_object* v___y_1521_ = _args[12];
lean_object* v___y_1522_ = _args[13];
lean_object* v___y_1523_ = _args[14];
lean_object* v___y_1524_ = _args[15];
lean_object* v___y_1525_ = _args[16];
lean_object* v___y_1526_ = _args[17];
lean_object* v___y_1527_ = _args[18];
lean_object* v___y_1528_ = _args[19];
_start:
{
uint8_t v___x_20523__boxed_1529_; lean_object* v_res_1530_; 
v___x_20523__boxed_1529_ = lean_unbox(v___x_1511_);
v_res_1530_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0(v___x_1509_, v_a_1510_, v___x_20523__boxed_1529_, v___x_1512_, v___x_1513_, v___x_1514_, v___x_1515_, v_tk_1516_, v_typesStx_1517_, v___x_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec(v___x_1518_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic(lean_object* v_x_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; 
v___x_1547_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0));
v___x_1548_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1));
v___x_1549_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1));
v___x_1550_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__1));
lean_inc(v_x_1537_);
v___x_1551_ = l_Lean_Syntax_isOfKind(v_x_1537_, v___x_1550_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; 
lean_dec(v_x_1537_);
v___x_1552_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1552_;
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1553_ = lean_unsigned_to_nat(1u);
v___x_1554_ = l_Lean_Syntax_getArg(v_x_1537_, v___x_1553_);
v___x_1555_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_1554_);
v___x_1556_ = l_Lean_Syntax_isOfKind(v___x_1554_, v___x_1555_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; 
lean_dec(v___x_1554_);
lean_dec(v_x_1537_);
v___x_1557_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1557_;
}
else
{
lean_object* v___x_1558_; lean_object* v_tk_1559_; lean_object* v_typesStx_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___x_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; 
v___x_1558_ = lean_unsigned_to_nat(0u);
v_tk_1559_ = l_Lean_Syntax_getArg(v_x_1537_, v___x_1558_);
v___x_1647_ = lean_unsigned_to_nat(2u);
v___x_1648_ = l_Lean_Syntax_getArg(v_x_1537_, v___x_1647_);
lean_dec(v_x_1537_);
v___x_1649_ = l_Lean_Syntax_isNone(v___x_1648_);
if (v___x_1649_ == 0)
{
uint8_t v___x_1650_; 
lean_inc(v___x_1648_);
v___x_1650_ = l_Lean_Syntax_matchesNull(v___x_1648_, v___x_1553_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; 
lean_dec(v___x_1648_);
lean_dec(v_tk_1559_);
lean_dec(v___x_1554_);
v___x_1651_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1651_;
}
else
{
lean_object* v_typesStx_1652_; 
v_typesStx_1652_ = l_Lean_Syntax_getArg(v___x_1648_, v___x_1558_);
lean_dec(v___x_1648_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1655_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_typesStx_1652_);
v___x_1656_ = l_Lean_Syntax_isOfKind(v_typesStx_1652_, v___x_1655_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; 
lean_dec(v_typesStx_1652_);
lean_dec(v_tk_1559_);
lean_dec(v___x_1554_);
v___x_1657_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1657_;
}
else
{
goto v___jp_1653_;
}
}
else
{
goto v___jp_1653_;
}
v___jp_1653_:
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1654_, 0, v_typesStx_1652_);
v_typesStx_1561_ = v___x_1654_;
v___y_1562_ = v_a_1538_;
v___y_1563_ = v_a_1539_;
v___y_1564_ = v_a_1540_;
v___y_1565_ = v_a_1541_;
v___y_1566_ = v_a_1542_;
v___y_1567_ = v_a_1543_;
v___y_1568_ = v_a_1544_;
v___y_1569_ = v_a_1545_;
goto v___jp_1560_;
}
}
}
else
{
lean_object* v___x_1658_; 
lean_dec(v___x_1648_);
v___x_1658_ = lean_box(0);
v_typesStx_1561_ = v___x_1658_;
v___y_1562_ = v_a_1538_;
v___y_1563_ = v_a_1539_;
v___y_1564_ = v_a_1540_;
v___y_1565_ = v_a_1541_;
v___y_1566_ = v_a_1542_;
v___y_1567_ = v_a_1543_;
v___y_1568_ = v_a_1544_;
v___y_1569_ = v_a_1545_;
goto v___jp_1560_;
}
v___jp_1560_:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1568_, v___y_1569_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1645_; 
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1645_ == 0)
{
lean_object* v_unused_1646_; 
v_unused_1646_ = lean_ctor_get(v___x_1570_, 0);
lean_dec(v_unused_1646_);
v___x_1572_ = v___x_1570_;
v_isShared_1573_ = v_isSharedCheck_1645_;
goto v_resetjp_1571_;
}
else
{
lean_dec(v___x_1570_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1645_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1574_; uint8_t v___x_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1574_ = lean_unsigned_to_nat(10u);
v___x_1575_ = 0;
v___x_1576_ = lean_unsigned_to_nat(100000u);
v___x_1577_ = 0;
v___x_1578_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_1578_, 0, v___x_1574_);
lean_ctor_set(v___x_1578_, 1, v___x_1576_);
lean_ctor_set_uint8(v___x_1578_, sizeof(void*)*2, v___x_1556_);
lean_ctor_set_uint8(v___x_1578_, sizeof(void*)*2 + 1, v___x_1556_);
lean_ctor_set_uint8(v___x_1578_, sizeof(void*)*2 + 2, v___x_1575_);
lean_ctor_set_uint8(v___x_1578_, sizeof(void*)*2 + 3, v___x_1556_);
lean_ctor_set_uint8(v___x_1578_, sizeof(void*)*2 + 4, v___x_1556_);
lean_ctor_set_uint8(v___x_1578_, sizeof(void*)*2 + 5, v___x_1556_);
lean_ctor_set_uint8(v___x_1578_, sizeof(void*)*2 + 6, v___x_1556_);
lean_ctor_set_uint8(v___x_1578_, sizeof(void*)*2 + 7, v___x_1556_);
lean_ctor_set_uint8(v___x_1578_, sizeof(void*)*2 + 8, v___x_1575_);
lean_ctor_set_uint8(v___x_1578_, sizeof(void*)*2 + 9, v___x_1575_);
lean_ctor_set_uint8(v___x_1578_, sizeof(void*)*2 + 10, v___x_1577_);
lean_inc(v___x_1554_);
v___x_1579_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_1554_, v___x_1578_, v___x_1556_, v___y_1562_, v___y_1568_, v___y_1569_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1581_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
lean_inc(v_typesStx_1561_);
v___x_1581_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_1561_, v_a_1580_, v___y_1568_, v___y_1569_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1583_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v___x_1583_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(v_a_1580_, v_a_1582_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1585_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___x_1583_, 1);
v___x_1585_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1563_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v___x_1585_, 1);
v___x_1587_ = lean_unsigned_to_nat(9u);
v___x_1588_ = lean_unsigned_to_nat(5u);
v___x_1589_ = lean_unsigned_to_nat(8u);
v___x_1590_ = lean_unsigned_to_nat(1000u);
v___x_1591_ = lean_unsigned_to_nat(1024u);
v___x_1592_ = lean_unsigned_to_nat(10000u);
v___x_1593_ = lean_unsigned_to_nat(1048576u);
v___x_1594_ = lean_unsigned_to_nat(50u);
v___x_1595_ = lean_box(0);
v___x_1596_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_1596_, 0, v___x_1587_);
lean_ctor_set(v___x_1596_, 1, v___x_1588_);
lean_ctor_set(v___x_1596_, 2, v___x_1589_);
lean_ctor_set(v___x_1596_, 3, v___x_1589_);
lean_ctor_set(v___x_1596_, 4, v___x_1590_);
lean_ctor_set(v___x_1596_, 5, v___x_1590_);
lean_ctor_set(v___x_1596_, 6, v___x_1576_);
lean_ctor_set(v___x_1596_, 7, v___x_1591_);
lean_ctor_set(v___x_1596_, 8, v___x_1592_);
lean_ctor_set(v___x_1596_, 9, v___x_1590_);
lean_ctor_set(v___x_1596_, 10, v___x_1593_);
lean_ctor_set(v___x_1596_, 11, v___x_1574_);
lean_ctor_set(v___x_1596_, 12, v___x_1594_);
lean_ctor_set(v___x_1596_, 13, v___x_1595_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14, v___x_1575_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 1, v___x_1575_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 2, v___x_1575_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 3, v___x_1575_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 4, v___x_1575_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 5, v___x_1556_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 6, v___x_1556_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 7, v___x_1556_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 8, v___x_1575_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 9, v___x_1575_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 10, v___x_1556_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 11, v___x_1575_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 12, v___x_1556_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 13, v___x_1556_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 14, v___x_1556_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 15, v___x_1556_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 16, v___x_1556_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 17, v___x_1575_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 18, v___x_1556_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 19, v___x_1556_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 20, v___x_1556_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 21, v___x_1556_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 22, v___x_1556_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 23, v___x_1556_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 24, v___x_1556_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 25, v___x_1556_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 26, v___x_1556_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 27, v___x_1556_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 28, v___x_1556_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 29, v___x_1556_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 30, v___x_1575_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 31, v___x_1556_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*14 + 32, v___x_1556_);
v___x_1597_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_1596_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1600_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1598_);
lean_dec_ref_known(v___x_1597_, 1);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v_a_1586_);
v___x_1600_ = v___x_1572_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1586_);
v___x_1600_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1601_; lean_object* v___f_1602_; lean_object* v___x_1603_; 
v___x_1601_ = lean_box(v___x_1575_);
v___f_1602_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___boxed), 20, 10);
lean_closure_set(v___f_1602_, 0, v___x_1600_);
lean_closure_set(v___f_1602_, 1, v_a_1584_);
lean_closure_set(v___f_1602_, 2, v___x_1601_);
lean_closure_set(v___f_1602_, 3, v___x_1547_);
lean_closure_set(v___f_1602_, 4, v___x_1548_);
lean_closure_set(v___f_1602_, 5, v___x_1549_);
lean_closure_set(v___f_1602_, 6, v___x_1554_);
lean_closure_set(v___f_1602_, 7, v_tk_1559_);
lean_closure_set(v___f_1602_, 8, v_typesStx_1561_);
lean_closure_set(v___f_1602_, 9, v___x_1558_);
v___x_1603_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___f_1602_, v_a_1598_, v___x_1595_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
return v___x_1603_;
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_dec(v_a_1586_);
lean_dec(v_a_1584_);
lean_del_object(v___x_1572_);
lean_dec(v_typesStx_1561_);
lean_dec(v_tk_1559_);
lean_dec(v___x_1554_);
v_a_1605_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1597_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1597_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec(v_a_1584_);
lean_del_object(v___x_1572_);
lean_dec(v_typesStx_1561_);
lean_dec(v_tk_1559_);
lean_dec(v___x_1554_);
v_a_1613_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1585_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1585_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_del_object(v___x_1572_);
lean_dec(v_typesStx_1561_);
lean_dec(v_tk_1559_);
lean_dec(v___x_1554_);
v_a_1621_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1583_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1583_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_dec(v_a_1580_);
lean_del_object(v___x_1572_);
lean_dec(v_typesStx_1561_);
lean_dec(v_tk_1559_);
lean_dec(v___x_1554_);
v_a_1629_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1581_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1581_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_del_object(v___x_1572_);
lean_dec(v_typesStx_1561_);
lean_dec(v_tk_1559_);
lean_dec(v___x_1554_);
v_a_1637_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1579_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1579_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
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
else
{
lean_dec(v_typesStx_1561_);
lean_dec(v_tk_1559_);
lean_dec(v___x_1554_);
return v___x_1570_;
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_1691_, uint8_t v___y_1692_, lean_object* v_x_1693_){
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
return v___x_1701_;
}
else
{
lean_object* v___x_1702_; uint8_t v___x_1703_; 
v___x_1702_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_1703_ = lean_string_dec_eq(v_str_1696_, v___x_1702_);
if (v___x_1703_ == 0)
{
return v___x_1703_;
}
else
{
return v_suppressElabErrors_1691_;
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
return v___x_1705_;
}
else
{
return v_suppressElabErrors_1691_;
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
return v___x_1711_;
}
else
{
lean_object* v___x_1712_; uint8_t v___x_1713_; 
v___x_1712_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_1713_ = lean_string_dec_eq(v_str_1708_, v___x_1712_);
if (v___x_1713_ == 0)
{
return v___x_1713_;
}
else
{
lean_object* v___x_1714_; uint8_t v___x_1715_; 
v___x_1714_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_1715_ = lean_string_dec_eq(v_str_1707_, v___x_1714_);
if (v___x_1715_ == 0)
{
return v___x_1715_;
}
else
{
return v_suppressElabErrors_1691_;
}
}
}
}
else
{
return v___y_1692_;
}
}
default: 
{
return v___y_1692_;
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
return v___x_1718_;
}
else
{
return v_suppressElabErrors_1691_;
}
}
default: 
{
return v___y_1692_;
}
}
}
else
{
return v___y_1692_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_1719_, lean_object* v___y_1720_, lean_object* v_x_1721_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1722_; uint8_t v___y_7481__boxed_1723_; uint8_t v_res_1724_; lean_object* v_r_1725_; 
v_suppressElabErrors_boxed_1722_ = lean_unbox(v_suppressElabErrors_1719_);
v___y_7481__boxed_1723_ = lean_unbox(v___y_1720_);
v_res_1724_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_1722_, v___y_7481__boxed_1723_, v_x_1721_);
lean_dec(v_x_1721_);
v_r_1725_ = lean_box(v_res_1724_);
return v_r_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(lean_object* v_ref_1727_, lean_object* v_msgData_1728_, uint8_t v_severity_1729_, uint8_t v_isSilent_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
uint8_t v___y_1737_; uint8_t v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v_toCold_1744_; lean_object* v___y_1745_; lean_object* v___y_1774_; lean_object* v___y_1775_; uint8_t v___y_1776_; uint8_t v___y_1777_; uint8_t v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; uint8_t v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; uint8_t v___y_1804_; uint8_t v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; uint8_t v___y_1811_; uint8_t v___y_1812_; uint8_t v___y_1813_; uint8_t v___x_1824_; uint8_t v___y_1826_; uint8_t v___y_1827_; uint8_t v___y_1828_; uint8_t v___y_1830_; uint8_t v___x_1838_; 
v___x_1824_ = 2;
v___x_1838_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1729_, v___x_1824_);
if (v___x_1838_ == 0)
{
v___y_1830_ = v___x_1838_;
goto v___jp_1829_;
}
else
{
uint8_t v___x_1839_; 
lean_inc_ref(v_msgData_1728_);
v___x_1839_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1728_);
v___y_1830_ = v___x_1839_;
goto v___jp_1829_;
}
v___jp_1736_:
{
lean_object* v_currNamespace_1746_; lean_object* v_openDecls_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v_env_1752_; lean_object* v_nextMacroScope_1753_; lean_object* v_ngen_1754_; lean_object* v_auxDeclNGen_1755_; lean_object* v_traceState_1756_; lean_object* v_cache_1757_; lean_object* v_recordedDeps_1758_; lean_object* v_messages_1759_; lean_object* v_infoState_1760_; lean_object* v_snapshotTasks_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1772_; 
v_currNamespace_1746_ = lean_ctor_get(v_toCold_1744_, 4);
v_openDecls_1747_ = lean_ctor_get(v_toCold_1744_, 5);
lean_inc(v_openDecls_1747_);
lean_inc(v_currNamespace_1746_);
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v_currNamespace_1746_);
lean_ctor_set(v___x_1748_, 1, v_openDecls_1747_);
v___x_1749_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
lean_ctor_set(v___x_1749_, 1, v___y_1739_);
lean_inc_ref(v___y_1740_);
lean_inc_ref(v___y_1741_);
v___x_1750_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1750_, 0, v___y_1741_);
lean_ctor_set(v___x_1750_, 1, v___y_1742_);
lean_ctor_set(v___x_1750_, 2, v___y_1743_);
lean_ctor_set(v___x_1750_, 3, v___y_1740_);
lean_ctor_set(v___x_1750_, 4, v___x_1749_);
lean_ctor_set_uint8(v___x_1750_, sizeof(void*)*5, v___y_1738_);
lean_ctor_set_uint8(v___x_1750_, sizeof(void*)*5 + 1, v___y_1737_);
lean_ctor_set_uint8(v___x_1750_, sizeof(void*)*5 + 2, v_isSilent_1730_);
v___x_1751_ = lean_st_ref_take(v___y_1745_);
v_env_1752_ = lean_ctor_get(v___x_1751_, 0);
v_nextMacroScope_1753_ = lean_ctor_get(v___x_1751_, 1);
v_ngen_1754_ = lean_ctor_get(v___x_1751_, 2);
v_auxDeclNGen_1755_ = lean_ctor_get(v___x_1751_, 3);
v_traceState_1756_ = lean_ctor_get(v___x_1751_, 4);
v_cache_1757_ = lean_ctor_get(v___x_1751_, 5);
v_recordedDeps_1758_ = lean_ctor_get(v___x_1751_, 6);
v_messages_1759_ = lean_ctor_get(v___x_1751_, 7);
v_infoState_1760_ = lean_ctor_get(v___x_1751_, 8);
v_snapshotTasks_1761_ = lean_ctor_get(v___x_1751_, 9);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1763_ = v___x_1751_;
v_isShared_1764_ = v_isSharedCheck_1772_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_snapshotTasks_1761_);
lean_inc(v_infoState_1760_);
lean_inc(v_messages_1759_);
lean_inc(v_recordedDeps_1758_);
lean_inc(v_cache_1757_);
lean_inc(v_traceState_1756_);
lean_inc(v_auxDeclNGen_1755_);
lean_inc(v_ngen_1754_);
lean_inc(v_nextMacroScope_1753_);
lean_inc(v_env_1752_);
lean_dec(v___x_1751_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1772_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1768_; 
v___x_1765_ = lean_box(0);
v___x_1766_ = l_Lean_MessageLog_add(v___x_1750_, v_messages_1759_);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 7, v___x_1766_);
v___x_1768_ = v___x_1763_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_env_1752_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_nextMacroScope_1753_);
lean_ctor_set(v_reuseFailAlloc_1771_, 2, v_ngen_1754_);
lean_ctor_set(v_reuseFailAlloc_1771_, 3, v_auxDeclNGen_1755_);
lean_ctor_set(v_reuseFailAlloc_1771_, 4, v_traceState_1756_);
lean_ctor_set(v_reuseFailAlloc_1771_, 5, v_cache_1757_);
lean_ctor_set(v_reuseFailAlloc_1771_, 6, v_recordedDeps_1758_);
lean_ctor_set(v_reuseFailAlloc_1771_, 7, v___x_1766_);
lean_ctor_set(v_reuseFailAlloc_1771_, 8, v_infoState_1760_);
lean_ctor_set(v_reuseFailAlloc_1771_, 9, v_snapshotTasks_1761_);
v___x_1768_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = lean_st_ref_put(v___y_1745_, v___x_1768_);
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1765_);
return v___x_1770_;
}
}
}
v___jp_1773_:
{
lean_object* v_fileName_1782_; lean_object* v_fileMap_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1799_; 
v_fileName_1782_ = lean_ctor_get(v___y_1780_, 0);
v_fileMap_1783_ = lean_ctor_get(v___y_1780_, 1);
v___x_1784_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1728_);
v___x_1785_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v___x_1784_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1788_ = v___x_1785_;
v_isShared_1789_ = v_isSharedCheck_1799_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1785_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1799_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_inc_ref_n(v_fileMap_1783_, 2);
v___x_1790_ = l_Lean_FileMap_toPosition(v_fileMap_1783_, v___y_1779_);
lean_dec(v___y_1779_);
v___x_1791_ = l_Lean_FileMap_toPosition(v_fileMap_1783_, v___y_1781_);
lean_dec(v___y_1781_);
v___x_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1791_);
v___x_1793_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___closed__0));
if (v___y_1778_ == 0)
{
lean_del_object(v___x_1788_);
lean_dec_ref(v___y_1775_);
v___y_1737_ = v___y_1777_;
v___y_1738_ = v___y_1776_;
v___y_1739_ = v_a_1786_;
v___y_1740_ = v___x_1793_;
v___y_1741_ = v_fileName_1782_;
v___y_1742_ = v___x_1790_;
v___y_1743_ = v___x_1792_;
v_toCold_1744_ = v___y_1774_;
v___y_1745_ = v___y_1734_;
goto v___jp_1736_;
}
else
{
uint8_t v___x_1794_; 
lean_inc(v_a_1786_);
v___x_1794_ = l_Lean_MessageData_hasTag(v___y_1775_, v_a_1786_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1797_; 
lean_dec_ref_known(v___x_1792_, 1);
lean_dec_ref(v___x_1790_);
lean_dec(v_a_1786_);
v___x_1795_ = lean_box(0);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 0, v___x_1795_);
v___x_1797_ = v___x_1788_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
else
{
lean_del_object(v___x_1788_);
v___y_1737_ = v___y_1777_;
v___y_1738_ = v___y_1776_;
v___y_1739_ = v_a_1786_;
v___y_1740_ = v___x_1793_;
v___y_1741_ = v_fileName_1782_;
v___y_1742_ = v___x_1790_;
v___y_1743_ = v___x_1792_;
v_toCold_1744_ = v___y_1774_;
v___y_1745_ = v___y_1734_;
goto v___jp_1736_;
}
}
}
}
v___jp_1800_:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Lean_Syntax_getTailPos_x3f(v___y_1806_, v___y_1805_);
lean_dec(v___y_1806_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_inc(v___y_1807_);
v___y_1774_ = v___y_1802_;
v___y_1775_ = v___y_1803_;
v___y_1776_ = v___y_1805_;
v___y_1777_ = v___y_1804_;
v___y_1778_ = v___y_1801_;
v___y_1779_ = v___y_1807_;
v___y_1780_ = v___y_1802_;
v___y_1781_ = v___y_1807_;
goto v___jp_1773_;
}
else
{
lean_object* v_val_1809_; 
v_val_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_val_1809_);
lean_dec_ref_known(v___x_1808_, 1);
v___y_1774_ = v___y_1802_;
v___y_1775_ = v___y_1803_;
v___y_1776_ = v___y_1805_;
v___y_1777_ = v___y_1804_;
v___y_1778_ = v___y_1801_;
v___y_1779_ = v___y_1807_;
v___y_1780_ = v___y_1802_;
v___y_1781_ = v_val_1809_;
goto v___jp_1773_;
}
}
v___jp_1810_:
{
lean_object* v_toCold_1814_; lean_object* v_ref_1815_; uint8_t v_suppressElabErrors_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___f_1819_; lean_object* v_ref_1820_; lean_object* v___x_1821_; 
v_toCold_1814_ = lean_ctor_get(v___y_1733_, 0);
v_ref_1815_ = lean_ctor_get(v___y_1733_, 2);
v_suppressElabErrors_1816_ = lean_ctor_get_uint8(v___y_1733_, sizeof(void*)*3 + 2);
v___x_1817_ = lean_box(v_suppressElabErrors_1816_);
v___x_1818_ = lean_box(v___y_1811_);
v___f_1819_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1819_, 0, v___x_1817_);
lean_closure_set(v___f_1819_, 1, v___x_1818_);
v_ref_1820_ = l_Lean_replaceRef(v_ref_1727_, v_ref_1815_);
v___x_1821_ = l_Lean_Syntax_getPos_x3f(v_ref_1820_, v___y_1812_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_unsigned_to_nat(0u);
v___y_1801_ = v_suppressElabErrors_1816_;
v___y_1802_ = v_toCold_1814_;
v___y_1803_ = v___f_1819_;
v___y_1804_ = v___y_1813_;
v___y_1805_ = v___y_1812_;
v___y_1806_ = v_ref_1820_;
v___y_1807_ = v___x_1822_;
goto v___jp_1800_;
}
else
{
lean_object* v_val_1823_; 
v_val_1823_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_val_1823_);
lean_dec_ref_known(v___x_1821_, 1);
v___y_1801_ = v_suppressElabErrors_1816_;
v___y_1802_ = v_toCold_1814_;
v___y_1803_ = v___f_1819_;
v___y_1804_ = v___y_1813_;
v___y_1805_ = v___y_1812_;
v___y_1806_ = v_ref_1820_;
v___y_1807_ = v_val_1823_;
goto v___jp_1800_;
}
}
v___jp_1825_:
{
if (v___y_1828_ == 0)
{
v___y_1811_ = v___y_1826_;
v___y_1812_ = v___y_1827_;
v___y_1813_ = v_severity_1729_;
goto v___jp_1810_;
}
else
{
v___y_1811_ = v___y_1826_;
v___y_1812_ = v___y_1827_;
v___y_1813_ = v___x_1824_;
goto v___jp_1810_;
}
}
v___jp_1829_:
{
if (v___y_1830_ == 0)
{
uint8_t v___x_1831_; uint8_t v___x_1832_; 
v___x_1831_ = 1;
v___x_1832_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1729_, v___x_1831_);
if (v___x_1832_ == 0)
{
v___y_1826_ = v___y_1830_;
v___y_1827_ = v___y_1830_;
v___y_1828_ = v___x_1832_;
goto v___jp_1825_;
}
else
{
lean_object* v___x_1833_; lean_object* v___x_1834_; uint8_t v___x_1835_; 
v___x_1833_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1733_);
v___x_1834_ = l_Lean_warningAsError;
v___x_1835_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v___x_1833_, v___x_1834_);
lean_dec_ref(v___x_1833_);
v___y_1826_ = v___y_1830_;
v___y_1827_ = v___y_1830_;
v___y_1828_ = v___x_1835_;
goto v___jp_1825_;
}
}
else
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
lean_dec_ref(v_msgData_1728_);
v___x_1836_ = lean_box(0);
v___x_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
return v___x_1837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_1840_, lean_object* v_msgData_1841_, lean_object* v_severity_1842_, lean_object* v_isSilent_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
uint8_t v_severity_boxed_1849_; uint8_t v_isSilent_boxed_1850_; lean_object* v_res_1851_; 
v_severity_boxed_1849_ = lean_unbox(v_severity_1842_);
v_isSilent_boxed_1850_ = lean_unbox(v_isSilent_1843_);
v_res_1851_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(v_ref_1840_, v_msgData_1841_, v_severity_boxed_1849_, v_isSilent_boxed_1850_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v_ref_1840_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(lean_object* v_msgData_1852_, uint8_t v_severity_1853_, uint8_t v_isSilent_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_ref_1860_; lean_object* v___x_1861_; 
v_ref_1860_ = lean_ctor_get(v___y_1857_, 2);
v___x_1861_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(v_ref_1860_, v_msgData_1852_, v_severity_1853_, v_isSilent_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0___boxed(lean_object* v_msgData_1862_, lean_object* v_severity_1863_, lean_object* v_isSilent_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
uint8_t v_severity_boxed_1870_; uint8_t v_isSilent_boxed_1871_; lean_object* v_res_1872_; 
v_severity_boxed_1870_ = lean_unbox(v_severity_1863_);
v_isSilent_boxed_1871_ = lean_unbox(v_isSilent_1864_);
v_res_1872_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(v_msgData_1862_, v_severity_boxed_1870_, v_isSilent_boxed_1871_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(lean_object* v_msgData_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
uint8_t v___x_1879_; uint8_t v___x_1880_; lean_object* v___x_1881_; 
v___x_1879_ = 1;
v___x_1880_ = 0;
v___x_1881_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(v_msgData_1873_, v___x_1879_, v___x_1880_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0___boxed(lean_object* v_msgData_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(v_msgData_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
return v_res_1888_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__0));
v___x_1891_ = l_Lean_stringToMessageData(v___x_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0(lean_object* v___x_1892_, lean_object* v___x_1893_, lean_object* v___x_1894_, lean_object* v___x_1895_, lean_object* v_tk_1896_, lean_object* v_typesStx_1897_, lean_object* v___x_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v_ref_1904_; uint8_t v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___y_1915_; 
v_ref_1904_ = lean_ctor_get(v___y_1901_, 2);
v___x_1905_ = 0;
v___x_1906_ = l_Lean_SourceInfo_fromRef(v_ref_1904_, v___x_1905_);
v___x_1907_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__1));
v___x_1908_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__2));
v___x_1909_ = l_Lean_Name_mkStr4(v___x_1892_, v___x_1893_, v___x_1894_, v___x_1908_);
v___x_1910_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3));
lean_inc(v___x_1906_);
v___x_1911_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1906_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5));
v___x_1913_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6);
if (lean_obj_tag(v_typesStx_1897_) == 1)
{
lean_object* v_val_1936_; lean_object* v___x_1937_; 
v_val_1936_ = lean_ctor_get(v_typesStx_1897_, 0);
lean_inc(v_val_1936_);
lean_dec_ref_known(v_typesStx_1897_, 1);
v___x_1937_ = l_Array_mkArray1___redArg(v_val_1936_);
v___y_1915_ = v___x_1937_;
goto v___jp_1914_;
}
else
{
lean_object* v___x_1938_; 
lean_dec(v_typesStx_1897_);
v___x_1938_ = lean_mk_empty_array_with_capacity(v___x_1898_);
v___y_1915_ = v___x_1938_;
goto v___jp_1914_;
}
v___jp_1914_:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1916_ = l_Array_append___redArg(v___x_1913_, v___y_1915_);
lean_dec_ref(v___y_1915_);
lean_inc(v___x_1906_);
v___x_1917_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1906_);
lean_ctor_set(v___x_1917_, 1, v___x_1912_);
lean_ctor_set(v___x_1917_, 2, v___x_1916_);
v___x_1918_ = l_Lean_Syntax_node3(v___x_1906_, v___x_1909_, v___x_1911_, v___x_1895_, v___x_1917_);
v___x_1919_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1, &l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1);
v___x_1920_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(v___x_1919_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1934_; 
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1934_ == 0)
{
lean_object* v_unused_1935_; 
v_unused_1935_ = lean_ctor_get(v___x_1920_, 0);
lean_dec(v_unused_1935_);
v___x_1922_ = v___x_1920_;
v_isShared_1923_ = v_isSharedCheck_1934_;
goto v_resetjp_1921_;
}
else
{
lean_dec(v___x_1920_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1934_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1907_);
lean_ctor_set(v___x_1924_, 1, v___x_1918_);
v___x_1925_ = lean_box(0);
v___x_1926_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1924_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
lean_ctor_set(v___x_1926_, 2, v___x_1925_);
lean_ctor_set(v___x_1926_, 3, v___x_1925_);
lean_ctor_set(v___x_1926_, 4, v___x_1925_);
lean_ctor_set(v___x_1926_, 5, v___x_1925_);
lean_inc(v_ref_1904_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set_tag(v___x_1922_, 1);
lean_ctor_set(v___x_1922_, 0, v_ref_1904_);
v___x_1928_ = v___x_1922_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_ref_1904_);
v___x_1928_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
lean_object* v___x_1929_; uint8_t v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1929_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__7));
v___x_1930_ = 4;
v___x_1931_ = l_Lean_MessageData_nil;
v___x_1932_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1896_, v___x_1926_, v___x_1928_, v___x_1929_, v___x_1925_, v___x_1930_, v___x_1931_, v___y_1901_, v___y_1902_);
return v___x_1932_;
}
}
}
else
{
lean_dec(v___x_1918_);
lean_dec(v_tk_1896_);
return v___x_1920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___boxed(lean_object* v___x_1939_, lean_object* v___x_1940_, lean_object* v___x_1941_, lean_object* v___x_1942_, lean_object* v_tk_1943_, lean_object* v_typesStx_1944_, lean_object* v___x_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0(v___x_1939_, v___x_1940_, v___x_1941_, v___x_1942_, v_tk_1943_, v_typesStx_1944_, v___x_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___x_1945_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic(lean_object* v_x_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; 
v___x_1970_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0));
v___x_1971_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1));
v___x_1972_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1));
v___x_1973_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0));
lean_inc(v_x_1960_);
v___x_1974_ = l_Lean_Syntax_isOfKind(v_x_1960_, v___x_1973_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; 
lean_dec(v_x_1960_);
v___x_1975_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1975_;
}
else
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; 
v___x_1976_ = lean_unsigned_to_nat(1u);
v___x_1977_ = l_Lean_Syntax_getArg(v_x_1960_, v___x_1976_);
v___x_1978_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_1977_);
v___x_1979_ = l_Lean_Syntax_isOfKind(v___x_1977_, v___x_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; 
lean_dec(v___x_1977_);
lean_dec(v_x_1960_);
v___x_1980_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1980_;
}
else
{
lean_object* v___x_1981_; lean_object* v_tk_1982_; lean_object* v_typesStx_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___x_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; 
v___x_1981_ = lean_unsigned_to_nat(0u);
v_tk_1982_ = l_Lean_Syntax_getArg(v_x_1960_, v___x_1981_);
v___x_2076_ = lean_unsigned_to_nat(2u);
v___x_2077_ = l_Lean_Syntax_getArg(v_x_1960_, v___x_2076_);
v___x_2078_ = l_Lean_Syntax_isNone(v___x_2077_);
if (v___x_2078_ == 0)
{
uint8_t v___x_2079_; 
lean_inc(v___x_2077_);
v___x_2079_ = l_Lean_Syntax_matchesNull(v___x_2077_, v___x_1976_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2080_; 
lean_dec(v___x_2077_);
lean_dec(v_tk_1982_);
lean_dec(v___x_1977_);
lean_dec(v_x_1960_);
v___x_2080_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2080_;
}
else
{
lean_object* v_typesStx_2081_; 
v_typesStx_2081_ = l_Lean_Syntax_getArg(v___x_2077_, v___x_1981_);
lean_dec(v___x_2077_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2084_; uint8_t v___x_2085_; 
v___x_2084_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_typesStx_2081_);
v___x_2085_ = l_Lean_Syntax_isOfKind(v_typesStx_2081_, v___x_2084_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; 
lean_dec(v_typesStx_2081_);
lean_dec(v_tk_1982_);
lean_dec(v___x_1977_);
lean_dec(v_x_1960_);
v___x_2086_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2086_;
}
else
{
goto v___jp_2082_;
}
}
else
{
goto v___jp_2082_;
}
v___jp_2082_:
{
lean_object* v___x_2083_; 
v___x_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2083_, 0, v_typesStx_2081_);
v_typesStx_1984_ = v___x_2083_;
v___y_1985_ = v_a_1961_;
v___y_1986_ = v_a_1962_;
v___y_1987_ = v_a_1963_;
v___y_1988_ = v_a_1964_;
v___y_1989_ = v_a_1965_;
v___y_1990_ = v_a_1966_;
v___y_1991_ = v_a_1967_;
v___y_1992_ = v_a_1968_;
goto v___jp_1983_;
}
}
}
else
{
lean_object* v___x_2087_; 
lean_dec(v___x_2077_);
v___x_2087_ = lean_box(0);
v_typesStx_1984_ = v___x_2087_;
v___y_1985_ = v_a_1961_;
v___y_1986_ = v_a_1962_;
v___y_1987_ = v_a_1963_;
v___y_1988_ = v_a_1964_;
v___y_1989_ = v_a_1965_;
v___y_1990_ = v_a_1966_;
v___y_1991_ = v_a_1967_;
v___y_1992_ = v_a_1968_;
goto v___jp_1983_;
}
v___jp_1983_:
{
lean_object* v___x_1993_; lean_object* v_path_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1993_ = lean_unsigned_to_nat(3u);
v_path_1994_ = l_Lean_Syntax_getArg(v_x_1960_, v___x_1993_);
lean_dec(v_x_1960_);
v___x_1995_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__2));
lean_inc(v_path_1994_);
v___x_1996_ = l_Lean_Syntax_isOfKind(v_path_1994_, v___x_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; 
lean_dec(v_path_1994_);
lean_dec(v_typesStx_1984_);
lean_dec(v_tk_1982_);
lean_dec(v___x_1977_);
v___x_1997_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1997_;
}
else
{
lean_object* v___f_1998_; lean_object* v___x_1999_; 
lean_inc(v_typesStx_1984_);
lean_inc(v___x_1977_);
v___f_1998_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___boxed), 12, 7);
lean_closure_set(v___f_1998_, 0, v___x_1970_);
lean_closure_set(v___f_1998_, 1, v___x_1971_);
lean_closure_set(v___f_1998_, 2, v___x_1972_);
lean_closure_set(v___f_1998_, 3, v___x_1977_);
lean_closure_set(v___f_1998_, 4, v_tk_1982_);
lean_closure_set(v___f_1998_, 5, v_typesStx_1984_);
lean_closure_set(v___f_1998_, 6, v___x_1981_);
v___x_1999_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2074_; 
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2074_ == 0)
{
lean_object* v_unused_2075_; 
v_unused_2075_ = lean_ctor_get(v___x_1999_, 0);
lean_dec(v_unused_2075_);
v___x_2001_ = v___x_1999_;
v_isShared_2002_ = v_isSharedCheck_2074_;
goto v_resetjp_2000_;
}
else
{
lean_dec(v___x_1999_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2074_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2003_; uint8_t v___x_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2003_ = lean_unsigned_to_nat(10u);
v___x_2004_ = 0;
v___x_2005_ = lean_unsigned_to_nat(100000u);
v___x_2006_ = 0;
v___x_2007_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_2007_, 0, v___x_2003_);
lean_ctor_set(v___x_2007_, 1, v___x_2005_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*2, v___x_1979_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*2 + 1, v___x_1979_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*2 + 2, v___x_2004_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*2 + 3, v___x_1979_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*2 + 4, v___x_1979_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*2 + 5, v___x_1979_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*2 + 6, v___x_1979_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*2 + 7, v___x_1979_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*2 + 8, v___x_2004_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*2 + 9, v___x_2004_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*2 + 10, v___x_2006_);
v___x_2008_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_1977_, v___x_2007_, v___x_1979_, v___y_1985_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2010_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2009_);
lean_dec_ref_known(v___x_2008_, 1);
v___x_2010_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_1984_, v_a_2009_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2010_, 1);
v___x_2012_ = l_Lean_TSyntax_getString(v_path_1994_);
lean_dec(v_path_1994_);
v___x_2013_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v___x_2012_, v_a_2009_, v_a_2011_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___x_2015_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
v___x_2015_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1986_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2016_);
lean_dec_ref_known(v___x_2015_, 1);
v___x_2017_ = lean_unsigned_to_nat(9u);
v___x_2018_ = lean_unsigned_to_nat(5u);
v___x_2019_ = lean_unsigned_to_nat(8u);
v___x_2020_ = lean_unsigned_to_nat(1000u);
v___x_2021_ = lean_unsigned_to_nat(1024u);
v___x_2022_ = lean_unsigned_to_nat(10000u);
v___x_2023_ = lean_unsigned_to_nat(1048576u);
v___x_2024_ = lean_unsigned_to_nat(50u);
v___x_2025_ = lean_box(0);
v___x_2026_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_2026_, 0, v___x_2017_);
lean_ctor_set(v___x_2026_, 1, v___x_2018_);
lean_ctor_set(v___x_2026_, 2, v___x_2019_);
lean_ctor_set(v___x_2026_, 3, v___x_2019_);
lean_ctor_set(v___x_2026_, 4, v___x_2020_);
lean_ctor_set(v___x_2026_, 5, v___x_2020_);
lean_ctor_set(v___x_2026_, 6, v___x_2005_);
lean_ctor_set(v___x_2026_, 7, v___x_2021_);
lean_ctor_set(v___x_2026_, 8, v___x_2022_);
lean_ctor_set(v___x_2026_, 9, v___x_2020_);
lean_ctor_set(v___x_2026_, 10, v___x_2023_);
lean_ctor_set(v___x_2026_, 11, v___x_2003_);
lean_ctor_set(v___x_2026_, 12, v___x_2024_);
lean_ctor_set(v___x_2026_, 13, v___x_2025_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14, v___x_2004_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 1, v___x_2004_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 2, v___x_2004_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 3, v___x_2004_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 4, v___x_2004_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 5, v___x_1979_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 6, v___x_1979_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 7, v___x_1979_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 8, v___x_2004_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 9, v___x_2004_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 10, v___x_1979_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 11, v___x_2004_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 12, v___x_1979_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 13, v___x_1979_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 14, v___x_1979_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 15, v___x_1979_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 16, v___x_1979_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 17, v___x_2004_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 18, v___x_1979_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 19, v___x_1979_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 20, v___x_1979_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 21, v___x_1979_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 22, v___x_1979_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 23, v___x_1979_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 24, v___x_1979_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 25, v___x_1979_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 26, v___x_1979_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 27, v___x_1979_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 28, v___x_1979_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 29, v___x_1979_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 30, v___x_2004_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 31, v___x_1979_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*14 + 32, v___x_1979_);
v___x_2027_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_2026_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v___x_2027_, 1);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v_a_2016_);
v___x_2030_ = v___x_2001_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2016_);
v___x_2030_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed), 13, 3);
lean_closure_set(v___x_2031_, 0, v___x_2030_);
lean_closure_set(v___x_2031_, 1, v_a_2014_);
lean_closure_set(v___x_2031_, 2, v___f_1998_);
v___x_2032_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___x_2031_, v_a_2028_, v___x_2025_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
return v___x_2032_;
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec(v_a_2016_);
lean_dec(v_a_2014_);
lean_del_object(v___x_2001_);
lean_dec_ref(v___f_1998_);
v_a_2034_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2027_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2027_);
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
lean_dec(v_a_2014_);
lean_del_object(v___x_2001_);
lean_dec_ref(v___f_1998_);
v_a_2042_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2015_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2015_);
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
lean_del_object(v___x_2001_);
lean_dec_ref(v___f_1998_);
v_a_2050_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2013_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2013_);
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
lean_del_object(v___x_2001_);
lean_dec_ref(v___f_1998_);
lean_dec(v_path_1994_);
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
lean_del_object(v___x_2001_);
lean_dec_ref(v___f_1998_);
lean_dec(v_path_1994_);
lean_dec(v_typesStx_1984_);
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
lean_dec_ref(v___f_1998_);
lean_dec(v_path_1994_);
lean_dec(v_typesStx_1984_);
lean_dec(v___x_1977_);
return v___x_1999_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___boxed(lean_object* v_x_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic(v_x_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_);
lean_dec(v_a_2096_);
lean_dec_ref(v_a_2095_);
lean_dec(v_a_2094_);
lean_dec_ref(v_a_2093_);
lean_dec(v_a_2092_);
lean_dec_ref(v_a_2091_);
lean_dec(v_a_2090_);
lean_dec_ref(v_a_2089_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1(){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2107_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2108_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0));
v___x_2109_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___closed__1));
v___x_2110_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___boxed), 10, 0);
v___x_2111_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2107_, v___x_2108_, v___x_2109_, v___x_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___boxed(lean_object* v_a_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1();
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0(lean_object* v___x_2114_, uint8_t v___x_2115_, lean_object* v___x_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2127_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1);
v___x_2128_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4);
v___x_2129_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5));
v___x_2130_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2130_, 0, v___x_2127_);
lean_ctor_set(v___x_2130_, 1, v___x_2128_);
lean_ctor_set(v___x_2130_, 2, v___x_2114_);
lean_ctor_set(v___x_2130_, 3, v___x_2129_);
lean_ctor_set_uint8(v___x_2130_, sizeof(void*)*4, v___x_2115_);
v___x_2131_ = lean_st_mk_ref(v___x_2130_);
v___x_2132_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_2116_, v___x_2131_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2142_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2135_ = v___x_2132_;
v_isShared_2136_ = v_isSharedCheck_2142_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2132_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2142_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2140_; 
v___x_2137_ = lean_st_ref_get(v___x_2131_);
lean_dec(v___x_2131_);
v___x_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2138_, 0, v_a_2133_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2138_);
v___x_2140_ = v___x_2135_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
else
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2150_; 
lean_dec(v___x_2131_);
v_a_2143_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2145_ = v___x_2132_;
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2132_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2146_ == 0)
{
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0___boxed(lean_object* v___x_2151_, lean_object* v___x_2152_, lean_object* v___x_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
uint8_t v___x_3453__boxed_2164_; lean_object* v_res_2165_; 
v___x_3453__boxed_2164_ = lean_unbox(v___x_2152_);
v_res_2165_ = l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0(v___x_2151_, v___x_3453__boxed_2164_, v___x_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec_ref(v___x_2153_);
return v_res_2165_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_2166_, lean_object* v_i_2167_, lean_object* v_k_2168_){
_start:
{
lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2169_ = lean_array_get_size(v_keys_2166_);
v___x_2170_ = lean_nat_dec_lt(v_i_2167_, v___x_2169_);
if (v___x_2170_ == 0)
{
lean_dec(v_i_2167_);
return v___x_2170_;
}
else
{
lean_object* v_k_x27_2171_; uint8_t v___x_2172_; 
v_k_x27_2171_ = lean_array_fget_borrowed(v_keys_2166_, v_i_2167_);
v___x_2172_ = l_Lean_instBEqMVarId_beq(v_k_2168_, v_k_x27_2171_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = lean_unsigned_to_nat(1u);
v___x_2174_ = lean_nat_add(v_i_2167_, v___x_2173_);
lean_dec(v_i_2167_);
v_i_2167_ = v___x_2174_;
goto _start;
}
else
{
lean_dec(v_i_2167_);
return v___x_2170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_2176_, lean_object* v_i_2177_, lean_object* v_k_2178_){
_start:
{
uint8_t v_res_2179_; lean_object* v_r_2180_; 
v_res_2179_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2176_, v_i_2177_, v_k_2178_);
lean_dec(v_k_2178_);
lean_dec_ref(v_keys_2176_);
v_r_2180_ = lean_box(v_res_2179_);
return v_r_2180_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2181_, size_t v_x_2182_, lean_object* v_x_2183_){
_start:
{
if (lean_obj_tag(v_x_2181_) == 0)
{
lean_object* v_es_2184_; lean_object* v___x_2185_; size_t v___x_2186_; size_t v___x_2187_; lean_object* v_j_2188_; lean_object* v___x_2189_; 
v_es_2184_ = lean_ctor_get(v_x_2181_, 0);
v___x_2185_ = lean_box(2);
v___x_2186_ = ((size_t)31ULL);
v___x_2187_ = lean_usize_land(v_x_2182_, v___x_2186_);
v_j_2188_ = lean_usize_to_nat(v___x_2187_);
v___x_2189_ = lean_array_get_borrowed(v___x_2185_, v_es_2184_, v_j_2188_);
lean_dec(v_j_2188_);
switch(lean_obj_tag(v___x_2189_))
{
case 0:
{
lean_object* v_key_2190_; uint8_t v___x_2191_; 
v_key_2190_ = lean_ctor_get(v___x_2189_, 0);
v___x_2191_ = l_Lean_instBEqMVarId_beq(v_x_2183_, v_key_2190_);
return v___x_2191_;
}
case 1:
{
lean_object* v_node_2192_; size_t v___x_2193_; size_t v___x_2194_; 
v_node_2192_ = lean_ctor_get(v___x_2189_, 0);
v___x_2193_ = ((size_t)5ULL);
v___x_2194_ = lean_usize_shift_right(v_x_2182_, v___x_2193_);
v_x_2181_ = v_node_2192_;
v_x_2182_ = v___x_2194_;
goto _start;
}
default: 
{
uint8_t v___x_2196_; 
v___x_2196_ = 0;
return v___x_2196_;
}
}
}
else
{
lean_object* v_ks_2197_; lean_object* v___x_2198_; uint8_t v___x_2199_; 
v_ks_2197_ = lean_ctor_get(v_x_2181_, 0);
v___x_2198_ = lean_unsigned_to_nat(0u);
v___x_2199_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_2197_, v___x_2198_, v_x_2183_);
return v___x_2199_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2200_, lean_object* v_x_2201_, lean_object* v_x_2202_){
_start:
{
size_t v_x_3559__boxed_2203_; uint8_t v_res_2204_; lean_object* v_r_2205_; 
v_x_3559__boxed_2203_ = lean_unbox_usize(v_x_2201_);
lean_dec(v_x_2201_);
v_res_2204_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_2200_, v_x_3559__boxed_2203_, v_x_2202_);
lean_dec(v_x_2202_);
lean_dec_ref(v_x_2200_);
v_r_2205_ = lean_box(v_res_2204_);
return v_r_2205_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(lean_object* v_x_2206_, lean_object* v_x_2207_){
_start:
{
uint64_t v___x_2208_; size_t v___x_2209_; uint8_t v___x_2210_; 
v___x_2208_ = l_Lean_instHashableMVarId_hash(v_x_2207_);
v___x_2209_ = lean_uint64_to_usize(v___x_2208_);
v___x_2210_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_2206_, v___x_2209_, v_x_2207_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_2211_, lean_object* v_x_2212_){
_start:
{
uint8_t v_res_2213_; lean_object* v_r_2214_; 
v_res_2213_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(v_x_2211_, v_x_2212_);
lean_dec(v_x_2212_);
lean_dec_ref(v_x_2211_);
v_r_2214_ = lean_box(v_res_2213_);
return v_r_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(lean_object* v_mvarId_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v___x_2218_; lean_object* v_mctx_2219_; lean_object* v_eAssignment_2220_; uint8_t v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2218_ = lean_st_ref_get(v___y_2216_);
v_mctx_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc_ref(v_mctx_2219_);
lean_dec(v___x_2218_);
v_eAssignment_2220_ = lean_ctor_get(v_mctx_2219_, 8);
lean_inc_ref(v_eAssignment_2220_);
lean_dec_ref(v_mctx_2219_);
v___x_2221_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(v_eAssignment_2220_, v_mvarId_2215_);
lean_dec_ref(v_eAssignment_2220_);
v___x_2222_ = lean_box(v___x_2221_);
v___x_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg___boxed(lean_object* v_mvarId_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(v_mvarId_2224_, v___y_2225_);
lean_dec(v___y_2225_);
lean_dec(v_mvarId_2224_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1(size_t v_sz_2228_, size_t v_i_2229_, lean_object* v_bs_2230_){
_start:
{
uint8_t v___x_2231_; 
v___x_2231_ = lean_usize_dec_lt(v_i_2229_, v_sz_2228_);
if (v___x_2231_ == 0)
{
return v_bs_2230_;
}
else
{
lean_object* v_v_2232_; lean_object* v_name_2233_; lean_object* v_type_2234_; lean_object* v_value_2235_; lean_object* v___x_2236_; lean_object* v_bs_x27_2237_; uint8_t v___x_2238_; uint8_t v___x_2239_; lean_object* v___x_2240_; size_t v___x_2241_; size_t v___x_2242_; lean_object* v___x_2243_; 
v_v_2232_ = lean_array_uget_borrowed(v_bs_2230_, v_i_2229_);
v_name_2233_ = lean_ctor_get(v_v_2232_, 0);
lean_inc(v_name_2233_);
v_type_2234_ = lean_ctor_get(v_v_2232_, 1);
lean_inc_ref(v_type_2234_);
v_value_2235_ = lean_ctor_get(v_v_2232_, 2);
lean_inc_ref(v_value_2235_);
v___x_2236_ = lean_unsigned_to_nat(0u);
v_bs_x27_2237_ = lean_array_uset(v_bs_2230_, v_i_2229_, v___x_2236_);
v___x_2238_ = 0;
v___x_2239_ = 0;
v___x_2240_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2240_, 0, v_name_2233_);
lean_ctor_set(v___x_2240_, 1, v_type_2234_);
lean_ctor_set(v___x_2240_, 2, v_value_2235_);
lean_ctor_set_uint8(v___x_2240_, sizeof(void*)*3, v___x_2238_);
lean_ctor_set_uint8(v___x_2240_, sizeof(void*)*3 + 1, v___x_2239_);
v___x_2241_ = ((size_t)1ULL);
v___x_2242_ = lean_usize_add(v_i_2229_, v___x_2241_);
v___x_2243_ = lean_array_uset(v_bs_x27_2237_, v_i_2229_, v___x_2240_);
v_i_2229_ = v___x_2242_;
v_bs_2230_ = v___x_2243_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1___boxed(lean_object* v_sz_2245_, lean_object* v_i_2246_, lean_object* v_bs_2247_){
_start:
{
size_t v_sz_boxed_2248_; size_t v_i_boxed_2249_; lean_object* v_res_2250_; 
v_sz_boxed_2248_ = lean_unbox_usize(v_sz_2245_);
lean_dec(v_sz_2245_);
v_i_boxed_2249_ = lean_unbox_usize(v_i_2246_);
lean_dec(v_i_2246_);
v_res_2250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1(v_sz_boxed_2248_, v_i_boxed_2249_, v_bs_2247_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize(lean_object* v_x_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_){
_start:
{
lean_object* v___x_2266_; uint8_t v___x_2267_; 
v___x_2266_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0));
lean_inc(v_x_2256_);
v___x_2267_ = l_Lean_Syntax_isOfKind(v_x_2256_, v___x_2266_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; 
lean_dec(v_x_2256_);
v___x_2268_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2268_;
}
else
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; uint8_t v___x_2272_; lean_object* v_types_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; 
v___x_2269_ = lean_unsigned_to_nat(1u);
v___x_2270_ = l_Lean_Syntax_getArg(v_x_2256_, v___x_2269_);
v___x_2271_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_2270_);
v___x_2272_ = l_Lean_Syntax_isOfKind(v___x_2270_, v___x_2271_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2394_; 
lean_dec(v___x_2270_);
lean_dec(v_x_2256_);
v___x_2394_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2394_;
}
else
{
lean_object* v___x_2395_; lean_object* v___x_2396_; uint8_t v___x_2397_; 
v___x_2395_ = lean_unsigned_to_nat(2u);
v___x_2396_ = l_Lean_Syntax_getArg(v_x_2256_, v___x_2395_);
lean_dec(v_x_2256_);
v___x_2397_ = l_Lean_Syntax_isNone(v___x_2396_);
if (v___x_2397_ == 0)
{
uint8_t v___x_2398_; 
lean_inc(v___x_2396_);
v___x_2398_ = l_Lean_Syntax_matchesNull(v___x_2396_, v___x_2269_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; 
lean_dec(v___x_2396_);
lean_dec(v___x_2270_);
v___x_2399_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2399_;
}
else
{
lean_object* v___x_2400_; lean_object* v_types_2401_; 
v___x_2400_ = lean_unsigned_to_nat(0u);
v_types_2401_ = l_Lean_Syntax_getArg(v___x_2396_, v___x_2400_);
lean_dec(v___x_2396_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2404_; uint8_t v___x_2405_; 
v___x_2404_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_types_2401_);
v___x_2405_ = l_Lean_Syntax_isOfKind(v_types_2401_, v___x_2404_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; 
lean_dec(v_types_2401_);
lean_dec(v___x_2270_);
v___x_2406_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2406_;
}
else
{
goto v___jp_2402_;
}
}
else
{
goto v___jp_2402_;
}
v___jp_2402_:
{
lean_object* v___x_2403_; 
v___x_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2403_, 0, v_types_2401_);
v_types_2274_ = v___x_2403_;
v___y_2275_ = v_a_2257_;
v___y_2276_ = v_a_2258_;
v___y_2277_ = v_a_2259_;
v___y_2278_ = v_a_2260_;
v___y_2279_ = v_a_2261_;
v___y_2280_ = v_a_2262_;
v___y_2281_ = v_a_2263_;
v___y_2282_ = v_a_2264_;
goto v___jp_2273_;
}
}
}
else
{
lean_object* v___x_2407_; 
lean_dec(v___x_2396_);
v___x_2407_ = lean_box(0);
v_types_2274_ = v___x_2407_;
v___y_2275_ = v_a_2257_;
v___y_2276_ = v_a_2258_;
v___y_2277_ = v_a_2259_;
v___y_2278_ = v_a_2260_;
v___y_2279_ = v_a_2261_;
v___y_2280_ = v_a_2262_;
v___y_2281_ = v_a_2263_;
v___y_2282_ = v_a_2264_;
goto v___jp_2273_;
}
}
v___jp_2273_:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_2281_, v___y_2282_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2392_; 
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2392_ == 0)
{
lean_object* v_unused_2393_; 
v_unused_2393_ = lean_ctor_get(v___x_2283_, 0);
lean_dec(v_unused_2393_);
v___x_2285_ = v___x_2283_;
v_isShared_2286_ = v_isSharedCheck_2392_;
goto v_resetjp_2284_;
}
else
{
lean_dec(v___x_2283_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2392_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; uint8_t v___x_2288_; lean_object* v___x_2289_; uint8_t v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2287_ = lean_unsigned_to_nat(10u);
v___x_2288_ = 0;
v___x_2289_ = lean_unsigned_to_nat(100000u);
v___x_2290_ = 0;
v___x_2291_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_2291_, 0, v___x_2287_);
lean_ctor_set(v___x_2291_, 1, v___x_2289_);
lean_ctor_set_uint8(v___x_2291_, sizeof(void*)*2, v___x_2272_);
lean_ctor_set_uint8(v___x_2291_, sizeof(void*)*2 + 1, v___x_2272_);
lean_ctor_set_uint8(v___x_2291_, sizeof(void*)*2 + 2, v___x_2288_);
lean_ctor_set_uint8(v___x_2291_, sizeof(void*)*2 + 3, v___x_2272_);
lean_ctor_set_uint8(v___x_2291_, sizeof(void*)*2 + 4, v___x_2272_);
lean_ctor_set_uint8(v___x_2291_, sizeof(void*)*2 + 5, v___x_2272_);
lean_ctor_set_uint8(v___x_2291_, sizeof(void*)*2 + 6, v___x_2272_);
lean_ctor_set_uint8(v___x_2291_, sizeof(void*)*2 + 7, v___x_2272_);
lean_ctor_set_uint8(v___x_2291_, sizeof(void*)*2 + 8, v___x_2288_);
lean_ctor_set_uint8(v___x_2291_, sizeof(void*)*2 + 9, v___x_2288_);
lean_ctor_set_uint8(v___x_2291_, sizeof(void*)*2 + 10, v___x_2290_);
v___x_2292_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_2270_, v___x_2291_, v___x_2272_, v___y_2275_, v___y_2281_, v___y_2282_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2294_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref_known(v___x_2292_, 1);
v___x_2294_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_types_2274_, v_a_2293_, v___y_2281_, v___y_2282_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2296_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref_known(v___x_2294_, 1);
v___x_2296_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2276_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2297_);
lean_dec_ref_known(v___x_2296_, 1);
v___x_2298_ = lean_unsigned_to_nat(9u);
v___x_2299_ = lean_unsigned_to_nat(5u);
v___x_2300_ = lean_unsigned_to_nat(8u);
v___x_2301_ = lean_unsigned_to_nat(1000u);
v___x_2302_ = lean_unsigned_to_nat(1024u);
v___x_2303_ = lean_unsigned_to_nat(10000u);
v___x_2304_ = lean_unsigned_to_nat(1048576u);
v___x_2305_ = lean_unsigned_to_nat(50u);
v___x_2306_ = lean_box(0);
v___x_2307_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_2307_, 0, v___x_2298_);
lean_ctor_set(v___x_2307_, 1, v___x_2299_);
lean_ctor_set(v___x_2307_, 2, v___x_2300_);
lean_ctor_set(v___x_2307_, 3, v___x_2300_);
lean_ctor_set(v___x_2307_, 4, v___x_2301_);
lean_ctor_set(v___x_2307_, 5, v___x_2301_);
lean_ctor_set(v___x_2307_, 6, v___x_2289_);
lean_ctor_set(v___x_2307_, 7, v___x_2302_);
lean_ctor_set(v___x_2307_, 8, v___x_2303_);
lean_ctor_set(v___x_2307_, 9, v___x_2301_);
lean_ctor_set(v___x_2307_, 10, v___x_2304_);
lean_ctor_set(v___x_2307_, 11, v___x_2287_);
lean_ctor_set(v___x_2307_, 12, v___x_2305_);
lean_ctor_set(v___x_2307_, 13, v___x_2306_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14, v___x_2288_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 1, v___x_2288_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 2, v___x_2288_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 3, v___x_2288_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 4, v___x_2288_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 5, v___x_2272_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 6, v___x_2272_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 7, v___x_2272_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 8, v___x_2288_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 9, v___x_2288_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 10, v___x_2272_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 11, v___x_2288_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 12, v___x_2272_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 13, v___x_2272_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 14, v___x_2272_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 15, v___x_2272_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 16, v___x_2272_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 17, v___x_2288_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 18, v___x_2272_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 19, v___x_2272_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 20, v___x_2272_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 21, v___x_2272_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 22, v___x_2272_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 23, v___x_2272_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 24, v___x_2272_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 25, v___x_2272_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 26, v___x_2272_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 27, v___x_2272_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 28, v___x_2272_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 29, v___x_2272_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 30, v___x_2288_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 31, v___x_2272_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*14 + 32, v___x_2272_);
v___x_2308_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_2307_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v___x_2311_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2308_, 1);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v_a_2295_);
v___x_2311_ = v___x_2285_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2295_);
v___x_2311_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___f_2315_; lean_object* v___x_2316_; 
v___x_2312_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v___x_2311_, v_a_2293_);
v___x_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2313_, 0, v_a_2297_);
v___x_2314_ = lean_box(v___x_2288_);
v___f_2315_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0___boxed), 13, 3);
lean_closure_set(v___f_2315_, 0, v___x_2313_);
lean_closure_set(v___f_2315_, 1, v___x_2314_);
lean_closure_set(v___f_2315_, 2, v___x_2312_);
v___x_2316_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___f_2315_, v_a_2309_, v___x_2306_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v_snd_2318_; lean_object* v_target_2319_; lean_object* v_hypotheses_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v_a_2323_; uint8_t v___x_2324_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2316_, 1);
v_snd_2318_ = lean_ctor_get(v_a_2317_, 1);
lean_inc(v_snd_2318_);
lean_dec(v_a_2317_);
v_target_2319_ = lean_ctor_get(v_snd_2318_, 2);
lean_inc_ref(v_target_2319_);
v_hypotheses_2320_ = lean_ctor_get(v_snd_2318_, 3);
lean_inc_ref(v_hypotheses_2320_);
lean_dec(v_snd_2318_);
v___x_2321_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_2319_);
lean_dec_ref(v_target_2319_);
v___x_2322_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(v___x_2321_, v___y_2280_);
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2323_);
lean_dec_ref(v___x_2322_);
v___x_2324_ = lean_unbox(v_a_2323_);
lean_dec(v_a_2323_);
if (v___x_2324_ == 0)
{
size_t v_sz_2325_; size_t v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v_sz_2325_ = lean_array_size(v_hypotheses_2320_);
v___x_2326_ = ((size_t)0ULL);
v___x_2327_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1(v_sz_2325_, v___x_2326_, v_hypotheses_2320_);
v___x_2328_ = l_Lean_MVarId_assertHypotheses(v___x_2321_, v___x_2327_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v_snd_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2339_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2329_);
lean_dec_ref_known(v___x_2328_, 1);
v_snd_2330_ = lean_ctor_get(v_a_2329_, 1);
v_isSharedCheck_2339_ = !lean_is_exclusive(v_a_2329_);
if (v_isSharedCheck_2339_ == 0)
{
lean_object* v_unused_2340_; 
v_unused_2340_ = lean_ctor_get(v_a_2329_, 0);
lean_dec(v_unused_2340_);
v___x_2332_ = v_a_2329_;
v_isShared_2333_ = v_isSharedCheck_2339_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_snd_2330_);
lean_dec(v_a_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2339_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; lean_object* v___x_2336_; 
v___x_2334_ = lean_box(0);
if (v_isShared_2333_ == 0)
{
lean_ctor_set_tag(v___x_2332_, 1);
lean_ctor_set(v___x_2332_, 1, v___x_2334_);
lean_ctor_set(v___x_2332_, 0, v_snd_2330_);
v___x_2336_ = v___x_2332_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_snd_2330_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v___x_2334_);
v___x_2336_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2336_, v___y_2276_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
return v___x_2337_;
}
}
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
v_a_2341_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2328_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2328_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
else
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
lean_dec(v___x_2321_);
lean_dec_ref(v_hypotheses_2320_);
v___x_2349_ = lean_box(0);
v___x_2350_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2349_, v___y_2276_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
return v___x_2350_;
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
v_a_2351_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2316_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2316_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v_a_2297_);
lean_dec(v_a_2295_);
lean_dec(v_a_2293_);
lean_del_object(v___x_2285_);
v_a_2360_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2308_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2308_);
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
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec(v_a_2295_);
lean_dec(v_a_2293_);
lean_del_object(v___x_2285_);
v_a_2368_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2296_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2296_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_dec(v_a_2293_);
lean_del_object(v___x_2285_);
v_a_2376_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2294_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2294_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
lean_del_object(v___x_2285_);
lean_dec(v_types_2274_);
v_a_2384_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2292_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2292_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
}
else
{
lean_dec(v_types_2274_);
lean_dec(v___x_2270_);
return v___x_2283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___boxed(lean_object* v_x_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Lean_Elab_Tactic_BVDecide_evalBVNormalize(v_x_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
lean_dec(v_a_2414_);
lean_dec_ref(v_a_2413_);
lean_dec(v_a_2412_);
lean_dec_ref(v_a_2411_);
lean_dec(v_a_2410_);
lean_dec_ref(v_a_2409_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0(lean_object* v_mvarId_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(v_mvarId_2419_, v___y_2425_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___boxed(lean_object* v_mvarId_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0(v_mvarId_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v_mvarId_2430_);
return v_res_2440_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0(lean_object* v_00_u03b2_2441_, lean_object* v_x_2442_, lean_object* v_x_2443_){
_start:
{
uint8_t v___x_2444_; 
v___x_2444_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(v_x_2442_, v_x_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2445_, lean_object* v_x_2446_, lean_object* v_x_2447_){
_start:
{
uint8_t v_res_2448_; lean_object* v_r_2449_; 
v_res_2448_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0(v_00_u03b2_2445_, v_x_2446_, v_x_2447_);
lean_dec(v_x_2447_);
lean_dec_ref(v_x_2446_);
v_r_2449_ = lean_box(v_res_2448_);
return v_r_2449_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2450_, lean_object* v_x_2451_, size_t v_x_2452_, lean_object* v_x_2453_){
_start:
{
uint8_t v___x_2454_; 
v___x_2454_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_2451_, v_x_2452_, v_x_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2455_, lean_object* v_x_2456_, lean_object* v_x_2457_, lean_object* v_x_2458_){
_start:
{
size_t v_x_3996__boxed_2459_; uint8_t v_res_2460_; lean_object* v_r_2461_; 
v_x_3996__boxed_2459_ = lean_unbox_usize(v_x_2457_);
lean_dec(v_x_2457_);
v_res_2460_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1(v_00_u03b2_2455_, v_x_2456_, v_x_3996__boxed_2459_, v_x_2458_);
lean_dec(v_x_2458_);
lean_dec_ref(v_x_2456_);
v_r_2461_ = lean_box(v_res_2460_);
return v_r_2461_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2462_, lean_object* v_keys_2463_, lean_object* v_vals_2464_, lean_object* v_heq_2465_, lean_object* v_i_2466_, lean_object* v_k_2467_){
_start:
{
uint8_t v___x_2468_; 
v___x_2468_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2463_, v_i_2466_, v_k_2467_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2469_, lean_object* v_keys_2470_, lean_object* v_vals_2471_, lean_object* v_heq_2472_, lean_object* v_i_2473_, lean_object* v_k_2474_){
_start:
{
uint8_t v_res_2475_; lean_object* v_r_2476_; 
v_res_2475_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2469_, v_keys_2470_, v_vals_2471_, v_heq_2472_, v_i_2473_, v_k_2474_);
lean_dec(v_k_2474_);
lean_dec_ref(v_vals_2471_);
lean_dec_ref(v_keys_2470_);
v_r_2476_ = lean_box(v_res_2475_);
return v_r_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1(){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2485_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2486_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0));
v___x_2487_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___closed__1));
v___x_2488_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___boxed), 10, 0);
v___x_2489_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2485_, v___x_2486_, v___x_2487_, v___x_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___boxed(lean_object* v_a_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1();
return v_res_2491_;
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
