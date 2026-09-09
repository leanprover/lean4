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
static const lean_array_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6_value;
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
lean_object* v_toCold_181_; lean_object* v_options_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v_toCold_181_ = lean_ctor_get(v___y_179_, 0);
v_options_182_ = lean_ctor_get(v_toCold_181_, 2);
v___x_183_ = l_Lean_Elab_pp_macroStack;
v___x_184_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_182_, v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; 
lean_dec(v_macroStack_178_);
v___x_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_185_, 0, v_msgData_177_);
return v___x_185_;
}
else
{
if (lean_obj_tag(v_macroStack_178_) == 0)
{
lean_object* v___x_186_; 
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v_msgData_177_);
return v___x_186_;
}
else
{
lean_object* v_head_187_; lean_object* v_after_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_203_; 
v_head_187_ = lean_ctor_get(v_macroStack_178_, 0);
lean_inc(v_head_187_);
v_after_188_ = lean_ctor_get(v_head_187_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v_head_187_);
if (v_isSharedCheck_203_ == 0)
{
lean_object* v_unused_204_; 
v_unused_204_ = lean_ctor_get(v_head_187_, 0);
lean_dec(v_unused_204_);
v___x_190_ = v_head_187_;
v_isShared_191_ = v_isSharedCheck_203_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_after_188_);
lean_dec(v_head_187_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_203_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_192_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_191_ == 0)
{
lean_ctor_set_tag(v___x_190_, 7);
lean_ctor_set(v___x_190_, 1, v___x_192_);
lean_ctor_set(v___x_190_, 0, v_msgData_177_);
v___x_194_ = v___x_190_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_msgData_177_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v___x_192_);
v___x_194_ = v_reuseFailAlloc_202_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v_msgData_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_195_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2);
v___x_196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_194_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v___x_197_ = l_Lean_MessageData_ofSyntax(v_after_188_);
v___x_198_ = l_Lean_indentD(v___x_197_);
v_msgData_199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_199_, 0, v___x_196_);
lean_ctor_set(v_msgData_199_, 1, v___x_198_);
v___x_200_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3(v_msgData_199_, v_macroStack_178_);
v___x_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
return v___x_201_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_205_, lean_object* v_macroStack_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_msgData_205_, v_macroStack_206_, v___y_207_);
lean_dec_ref(v___y_207_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(lean_object* v_msg_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_ref_218_; lean_object* v___x_219_; lean_object* v_a_220_; lean_object* v_macroStack_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_232_; 
v_ref_218_ = lean_ctor_get(v___y_215_, 2);
v___x_219_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v_msg_210_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
v_a_220_ = lean_ctor_get(v___x_219_, 0);
lean_inc(v_a_220_);
lean_dec_ref(v___x_219_);
v_macroStack_221_ = lean_ctor_get(v___y_211_, 1);
v___x_222_ = l_Lean_Elab_getBetterRef(v_ref_218_, v_macroStack_221_);
lean_inc(v_macroStack_221_);
v___x_223_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_a_220_, v_macroStack_221_, v___y_215_);
v_a_224_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_232_ == 0)
{
v___x_226_ = v___x_223_;
v_isShared_227_ = v_isSharedCheck_232_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_223_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_232_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_222_);
lean_ctor_set(v___x_228_, 1, v_a_224_);
if (v_isShared_227_ == 0)
{
lean_ctor_set_tag(v___x_226_, 1);
lean_ctor_set(v___x_226_, 0, v___x_228_);
v___x_230_ = v___x_226_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg___boxed(lean_object* v_msg_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v_msg_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
return v_res_241_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__0));
v___x_244_ = l_Lean_stringToMessageData(v___x_243_);
return v___x_244_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__2));
v___x_247_ = l_Lean_stringToMessageData(v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_toCold_255_; lean_object* v_fileName_256_; lean_object* v___x_257_; 
v_toCold_255_ = lean_ctor_get(v_a_252_, 0);
v_fileName_256_ = lean_ctor_get(v_toCold_255_, 0);
lean_inc_ref(v_fileName_256_);
v___x_257_ = l_System_FilePath_parent(v_fileName_256_);
if (lean_obj_tag(v___x_257_) == 1)
{
lean_object* v_val_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_265_; 
v_val_258_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_265_ == 0)
{
v___x_260_ = v___x_257_;
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_val_258_);
lean_dec(v___x_257_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_261_ == 0)
{
lean_ctor_set_tag(v___x_260_, 0);
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_val_258_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec(v___x_257_);
v___x_266_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1, &l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1);
lean_inc_ref(v_fileName_256_);
v___x_267_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_267_, 0, v_fileName_256_);
v___x_268_ = l_Lean_MessageData_ofFormat(v___x_267_);
v___x_269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_266_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3, &l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3);
v___x_271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_269_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v___x_271_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___boxed(lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
lean_dec_ref(v_a_275_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0(lean_object* v_00_u03b1_281_, lean_object* v_msg_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v_msg_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___boxed(lean_object* v_00_u03b1_291_, lean_object* v_msg_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0(v_00_u03b1_291_, v_msg_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1(lean_object* v_msgData_301_, lean_object* v_macroStack_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_msgData_301_, v_macroStack_302_, v___y_307_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___boxed(lean_object* v_msgData_311_, lean_object* v_macroStack_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1(v_msgData_311_, v_macroStack_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(lean_object* v_lratPath_321_, lean_object* v_cfg_322_, lean_object* v_types_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_331_, 1);
v___x_333_ = l_System_FilePath_join(v_a_332_, v_lratPath_321_);
v___x_334_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new(v___x_333_, v_cfg_322_, v_types_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_);
return v___x_334_;
}
else
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
lean_dec(v_types_323_);
lean_dec_ref(v_cfg_322_);
lean_dec_ref(v_lratPath_321_);
v_a_335_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___x_331_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_331_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext___boxed(lean_object* v_lratPath_343_, lean_object* v_cfg_344_, lean_object* v_types_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v_lratPath_343_, v_cfg_344_, v_types_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0(lean_object* v_g_354_, lean_object* v___x_355_, lean_object* v___x_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(v_g_354_, v___x_355_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; 
v_unused_374_ = lean_ctor_get(v___x_366_, 0);
lean_dec(v_unused_374_);
v___x_368_ = v___x_366_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_dec(v___x_366_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_356_);
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_356_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
v_a_375_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_366_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_366_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0___boxed(lean_object* v_g_383_, lean_object* v___x_384_, lean_object* v___x_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0(v_g_383_, v___x_384_, v___x_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(lean_object* v_g_396_, lean_object* v_hypotheses_397_, lean_object* v_ctx_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___f_408_; lean_object* v___x_409_; 
v___x_406_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed), 9, 1);
lean_closure_set(v___x_406_, 0, v_ctx_398_);
v___x_407_ = lean_box(0);
v___f_408_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0___boxed), 12, 3);
lean_closure_set(v___f_408_, 0, v_g_396_);
lean_closure_set(v___f_408_, 1, v___x_406_);
lean_closure_set(v___f_408_, 2, v___x_407_);
v___x_409_ = l_Lean_Meta_Tactic_BVDecide_M_run___redArg(v___f_408_, v_hypotheses_397_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___boxed(lean_object* v_g_410_, lean_object* v_hypotheses_411_, lean_object* v_ctx_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(v_g_410_, v_hypotheses_411_, v_ctx_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
return v_res_420_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0(void){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_421_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
return v___x_423_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1);
v___x_425_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
lean_ctor_set(v___x_425_, 2, v___x_424_);
lean_ctor_set(v___x_425_, 3, v___x_424_);
return v___x_425_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = lean_box(0);
v___x_427_ = lean_unsigned_to_nat(16u);
v___x_428_ = lean_mk_array(v___x_427_, v___x_426_);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3);
v___x_430_ = lean_unsigned_to_nat(0u);
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v___x_429_);
return v___x_431_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4);
v___x_433_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
lean_ctor_set(v___x_433_, 2, v___x_432_);
lean_ctor_set(v___x_433_, 3, v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck(lean_object* v_target_436_, lean_object* v_ctx_437_, lean_object* v_warn_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___y_456_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_449_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2);
v___x_450_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5);
v___x_451_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6));
v___x_452_ = 0;
v___x_453_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_453_, 0, v___x_449_);
lean_ctor_set(v___x_453_, 1, v___x_450_);
lean_ctor_set(v___x_453_, 2, v_target_436_);
lean_ctor_set(v___x_453_, 3, v___x_451_);
lean_ctor_set_uint8(v___x_453_, sizeof(void*)*4, v___x_452_);
v___x_454_ = lean_st_mk_ref(v___x_453_);
lean_inc_ref(v_ctx_437_);
v___x_466_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_ctx_437_);
v___x_467_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_466_, v___x_454_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_);
lean_dec_ref(v___x_466_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; uint8_t v___x_469_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
lean_dec_ref_known(v___x_467_, 1);
v___x_469_ = lean_unbox(v_a_468_);
lean_dec(v_a_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v_target_472_; lean_object* v_hypotheses_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
lean_dec_ref(v_warn_438_);
v___x_470_ = lean_st_ref_get(v___x_454_);
v___x_471_ = lean_st_ref_get(v___x_454_);
v_target_472_ = lean_ctor_get(v___x_470_, 2);
lean_inc_ref(v_target_472_);
lean_dec(v___x_470_);
v_hypotheses_473_ = lean_ctor_get(v___x_471_, 3);
lean_inc_ref(v_hypotheses_473_);
lean_dec(v___x_471_);
v___x_474_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_472_);
lean_dec_ref(v_target_472_);
v___x_475_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(v___x_474_, v_hypotheses_473_, v_ctx_437_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_);
v___y_456_ = v___x_475_;
goto v___jp_455_;
}
else
{
lean_object* v___x_476_; 
lean_dec_ref(v_ctx_437_);
lean_inc(v_a_447_);
lean_inc_ref(v_a_446_);
lean_inc(v_a_445_);
lean_inc_ref(v_a_444_);
v___x_476_ = lean_apply_5(v_warn_438_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, lean_box(0));
v___y_456_ = v___x_476_;
goto v___jp_455_;
}
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
lean_dec(v___x_454_);
lean_dec_ref(v_warn_438_);
lean_dec_ref(v_ctx_437_);
v_a_477_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_467_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_467_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
v___jp_455_:
{
if (lean_obj_tag(v___y_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_465_; 
v_a_457_ = lean_ctor_get(v___y_456_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___y_456_);
if (v_isSharedCheck_465_ == 0)
{
v___x_459_ = v___y_456_;
v_isShared_460_ = v_isSharedCheck_465_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___y_456_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_465_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_461_ = lean_st_ref_get(v___x_454_);
lean_dec(v___x_454_);
lean_dec(v___x_461_);
if (v_isShared_460_ == 0)
{
v___x_463_ = v___x_459_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_457_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
else
{
lean_dec(v___x_454_);
return v___y_456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed(lean_object* v_target_485_, lean_object* v_ctx_486_, lean_object* v_warn_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck(v_target_485_, v_ctx_486_, v_warn_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_495_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(lean_object* v___y_499_){
_start:
{
lean_object* v_ref_501_; uint8_t v___x_502_; lean_object* v___x_503_; 
v_ref_501_ = lean_ctor_get(v___y_499_, 2);
v___x_502_ = 0;
v___x_503_ = l_Lean_Syntax_getPos_x3f(v_ref_501_, v___x_502_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_unsigned_to_nat(0u);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
else
{
lean_object* v_val_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
v_val_506_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_503_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_val_506_);
lean_dec(v___x_503_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set_tag(v___x_508_, 0);
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_val_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg___boxed(lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v___y_514_);
lean_dec_ref(v___y_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0(lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v___y_521_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___boxed(lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0(v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
return v_res_532_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__2));
v___x_537_ = l_Lean_stringToMessageData(v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__4));
v___x_540_ = l_Lean_stringToMessageData(v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_toCold_548_; lean_object* v_fileName_549_; lean_object* v_fileMap_550_; lean_object* v___x_551_; 
v_toCold_548_ = lean_ctor_get(v_a_545_, 0);
v_fileName_549_ = lean_ctor_get(v_toCold_548_, 0);
v_fileMap_550_ = lean_ctor_get(v_toCold_548_, 1);
lean_inc_ref(v_fileName_549_);
v___x_551_ = l_System_FilePath_fileName(v_fileName_549_);
if (lean_obj_tag(v___x_551_) == 1)
{
lean_object* v_val_552_; lean_object* v___x_553_; 
v_val_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_val_552_);
lean_dec_ref_known(v___x_551_, 1);
v___x_553_ = l_Lean_Elab_Term_getDeclName_x3f___redArg(v_a_541_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v___x_553_, 1);
if (lean_obj_tag(v_a_554_) == 1)
{
lean_object* v_val_555_; lean_object* v___x_556_; lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_580_; 
v_val_555_ = lean_ctor_get(v_a_554_, 0);
lean_inc(v_val_555_);
lean_dec_ref_known(v_a_554_, 1);
v___x_556_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v_a_545_);
v_a_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_580_ == 0)
{
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_580_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_580_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v_line_562_; lean_object* v_column_563_; lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
lean_inc_ref(v_fileMap_550_);
v___x_561_ = l_Lean_FileMap_toPosition(v_fileMap_550_, v_a_557_);
lean_dec(v_a_557_);
v_line_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_line_562_);
v_column_563_ = lean_ctor_get(v___x_561_, 1);
lean_inc(v_column_563_);
lean_dec_ref(v___x_561_);
v___x_564_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__0));
v___x_565_ = lean_string_append(v_val_552_, v___x_564_);
v___x_566_ = 1;
v___x_567_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_555_, v___x_566_);
v___x_568_ = lean_string_append(v___x_565_, v___x_567_);
lean_dec_ref(v___x_567_);
v___x_569_ = lean_string_append(v___x_568_, v___x_564_);
v___x_570_ = l_Nat_reprFast(v_line_562_);
v___x_571_ = lean_string_append(v___x_569_, v___x_570_);
lean_dec_ref(v___x_570_);
v___x_572_ = lean_string_append(v___x_571_, v___x_564_);
v___x_573_ = l_Nat_reprFast(v_column_563_);
v___x_574_ = lean_string_append(v___x_572_, v___x_573_);
lean_dec_ref(v___x_573_);
v___x_575_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__1));
v___x_576_ = lean_string_append(v___x_574_, v___x_575_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_576_);
v___x_578_ = v___x_559_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; 
lean_dec(v_a_554_);
lean_dec(v_val_552_);
v___x_581_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3, &l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3);
v___x_582_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v___x_581_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
return v___x_582_;
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec(v_val_552_);
v_a_583_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_553_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_553_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; 
lean_dec(v___x_551_);
v___x_591_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5, &l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5);
v___x_592_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v___x_591_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
return v___x_592_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___boxed(lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(lean_object* v_cfg_601_, lean_object* v_types_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_612_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_a_611_);
lean_dec_ref_known(v___x_610_, 1);
v___x_612_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v_a_611_, v_cfg_601_, v_types_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_);
return v___x_612_;
}
else
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
lean_dec(v_types_602_);
lean_dec_ref(v_cfg_601_);
v_a_613_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_610_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_610_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext___boxed(lean_object* v_cfg_621_, lean_object* v_types_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(v_cfg_621_, v_types_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorIdx(lean_object* v_x_631_){
_start:
{
if (lean_obj_tag(v_x_631_) == 0)
{
lean_object* v___x_632_; 
v___x_632_ = lean_unsigned_to_nat(0u);
return v___x_632_;
}
else
{
lean_object* v___x_633_; 
v___x_633_ = lean_unsigned_to_nat(1u);
return v___x_633_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorIdx___boxed(lean_object* v_x_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorIdx(v_x_634_);
lean_dec(v_x_634_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(lean_object* v_t_636_, lean_object* v_k_637_){
_start:
{
if (lean_obj_tag(v_t_636_) == 0)
{
return v_k_637_;
}
else
{
lean_object* v_path_638_; lean_object* v___x_639_; 
v_path_638_ = lean_ctor_get(v_t_636_, 0);
lean_inc_ref(v_path_638_);
lean_dec_ref_known(v_t_636_, 1);
v___x_639_ = lean_apply_1(v_k_637_, v_path_638_);
return v___x_639_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim(lean_object* v_motive_640_, lean_object* v_ctorIdx_641_, lean_object* v_t_642_, lean_object* v_h_643_, lean_object* v_k_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_642_, v_k_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___boxed(lean_object* v_motive_646_, lean_object* v_ctorIdx_647_, lean_object* v_t_648_, lean_object* v_h_649_, lean_object* v_k_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim(v_motive_646_, v_ctorIdx_647_, v_t_648_, v_h_649_, v_k_650_);
lean_dec(v_ctorIdx_647_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_normalize_elim___redArg(lean_object* v_t_652_, lean_object* v_normalize_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_652_, v_normalize_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_normalize_elim(lean_object* v_motive_655_, lean_object* v_t_656_, lean_object* v_h_657_, lean_object* v_normalize_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_656_, v_normalize_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_check_elim___redArg(lean_object* v_t_660_, lean_object* v_check_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_660_, v_check_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_check_elim(lean_object* v_motive_663_, lean_object* v_t_664_, lean_object* v_h_665_, lean_object* v_check_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_664_, v_check_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0(lean_object* v_x_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v___x_679_; 
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
lean_inc(v___y_671_);
lean_inc_ref(v___y_670_);
lean_inc(v___y_669_);
v___x_679_ = lean_apply_10(v_x_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, lean_box(0));
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0___boxed(lean_object* v_x_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0(v_x_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(lean_object* v_mvarId_692_, lean_object* v_x_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v___f_704_; lean_object* v___x_705_; 
lean_inc(v___y_698_);
lean_inc_ref(v___y_697_);
lean_inc(v___y_696_);
lean_inc_ref(v___y_695_);
lean_inc(v___y_694_);
v___f_704_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_704_, 0, v_x_693_);
lean_closure_set(v___f_704_, 1, v___y_694_);
lean_closure_set(v___f_704_, 2, v___y_695_);
lean_closure_set(v___f_704_, 3, v___y_696_);
lean_closure_set(v___f_704_, 4, v___y_697_);
lean_closure_set(v___f_704_, 5, v___y_698_);
v___x_705_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_692_, v___f_704_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
if (lean_obj_tag(v___x_705_) == 0)
{
return v___x_705_;
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_705_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_705_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___boxed(lean_object* v_mvarId_714_, lean_object* v_x_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v_mvarId_714_, v_x_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1(lean_object* v_00_u03b1_727_, lean_object* v_mvarId_728_, lean_object* v_x_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v_mvarId_728_, v_x_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___boxed(lean_object* v_00_u03b1_741_, lean_object* v_mvarId_742_, lean_object* v_x_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1(v_00_u03b1_741_, v_mvarId_742_, v_x_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(lean_object* v_e_755_){
_start:
{
if (lean_obj_tag(v_e_755_) == 0)
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_765_; 
v_a_757_ = lean_ctor_get(v_e_755_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v_e_755_);
if (v_isSharedCheck_765_ == 0)
{
v___x_759_ = v_e_755_;
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v_e_755_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_761_ = lean_mk_io_user_error(v_a_757_);
if (v_isShared_760_ == 0)
{
lean_ctor_set_tag(v___x_759_, 1);
lean_ctor_set(v___x_759_, 0, v___x_761_);
v___x_763_ = v___x_759_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
v_a_766_ = lean_ctor_get(v_e_755_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v_e_755_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v_e_755_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v_e_755_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
lean_ctor_set_tag(v___x_768_, 0);
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg___boxed(lean_object* v_e_774_, lean_object* v_a_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v_e_774_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2(lean_object* v_00_u03b1_777_, lean_object* v_e_778_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v_e_778_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___boxed(lean_object* v_00_u03b1_781_, lean_object* v_e_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2(v_00_u03b1_781_, v_e_782_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(lean_object* v_msg_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_ref_791_; lean_object* v___x_792_; lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_801_; 
v_ref_791_ = lean_ctor_get(v___y_788_, 2);
v___x_792_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v_msg_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
v_a_793_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_801_ == 0)
{
v___x_795_ = v___x_792_;
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_792_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
lean_inc(v_ref_791_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_ref_791_);
lean_ctor_set(v___x_797_, 1, v_a_793_);
if (v_isShared_796_ == 0)
{
lean_ctor_set_tag(v___x_795_, 1);
lean_ctor_set(v___x_795_, 0, v___x_797_);
v___x_799_ = v___x_795_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg___boxed(lean_object* v_msg_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(v_msg_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(lean_object* v_target_809_, lean_object* v_ctx_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_exprDef_821_; lean_object* v_certDef_822_; lean_object* v_reflectionDef_823_; lean_object* v_solver_824_; lean_object* v_lratPath_825_; lean_object* v_config_826_; lean_object* v_restrictedTypes_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_953_; 
v_exprDef_821_ = lean_ctor_get(v_ctx_810_, 0);
v_certDef_822_ = lean_ctor_get(v_ctx_810_, 1);
v_reflectionDef_823_ = lean_ctor_get(v_ctx_810_, 2);
v_solver_824_ = lean_ctor_get(v_ctx_810_, 3);
v_lratPath_825_ = lean_ctor_get(v_ctx_810_, 4);
v_config_826_ = lean_ctor_get(v_ctx_810_, 5);
v_restrictedTypes_827_ = lean_ctor_get(v_ctx_810_, 6);
v_isSharedCheck_953_ = !lean_is_exclusive(v_ctx_810_);
if (v_isSharedCheck_953_ == 0)
{
v___x_829_ = v_ctx_810_;
v_isShared_830_ = v_isSharedCheck_953_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_restrictedTypes_827_);
lean_inc(v_config_826_);
lean_inc(v_lratPath_825_);
lean_inc(v_solver_824_);
lean_inc(v_reflectionDef_823_);
lean_inc(v_certDef_822_);
lean_inc(v_exprDef_821_);
lean_dec(v_ctx_810_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_953_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v_timeout_853_; uint8_t v_trimProofs_854_; uint8_t v_binaryProofs_855_; uint8_t v_acNf_856_; uint8_t v_andFlattening_857_; uint8_t v_embeddedConstraintSubst_858_; uint8_t v_structures_859_; uint8_t v_fixedInt_860_; uint8_t v_enums_861_; uint8_t v_graphviz_862_; lean_object* v_maxSteps_863_; uint8_t v_shortCircuit_864_; uint8_t v_solverMode_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_952_; 
v_timeout_853_ = lean_ctor_get(v_config_826_, 0);
v_trimProofs_854_ = lean_ctor_get_uint8(v_config_826_, sizeof(void*)*2);
v_binaryProofs_855_ = lean_ctor_get_uint8(v_config_826_, sizeof(void*)*2 + 1);
v_acNf_856_ = lean_ctor_get_uint8(v_config_826_, sizeof(void*)*2 + 2);
v_andFlattening_857_ = lean_ctor_get_uint8(v_config_826_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_858_ = lean_ctor_get_uint8(v_config_826_, sizeof(void*)*2 + 4);
v_structures_859_ = lean_ctor_get_uint8(v_config_826_, sizeof(void*)*2 + 5);
v_fixedInt_860_ = lean_ctor_get_uint8(v_config_826_, sizeof(void*)*2 + 6);
v_enums_861_ = lean_ctor_get_uint8(v_config_826_, sizeof(void*)*2 + 7);
v_graphviz_862_ = lean_ctor_get_uint8(v_config_826_, sizeof(void*)*2 + 8);
v_maxSteps_863_ = lean_ctor_get(v_config_826_, 1);
v_shortCircuit_864_ = lean_ctor_get_uint8(v_config_826_, sizeof(void*)*2 + 9);
v_solverMode_865_ = lean_ctor_get_uint8(v_config_826_, sizeof(void*)*2 + 10);
v_isSharedCheck_952_ = !lean_is_exclusive(v_config_826_);
if (v_isSharedCheck_952_ == 0)
{
v___x_867_ = v_config_826_;
v_isShared_868_ = v_isSharedCheck_952_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_maxSteps_863_);
lean_inc(v_timeout_853_);
lean_dec(v_config_826_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_952_;
goto v_resetjp_866_;
}
v___jp_831_:
{
lean_object* v___x_841_; 
v___x_841_ = l_System_FilePath_fileName(v_lratPath_825_);
if (lean_obj_tag(v___x_841_) == 1)
{
lean_object* v_val_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_850_; 
v_val_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_850_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_val_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_val_842_);
v___x_847_ = v_reuseFailAlloc_849_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; 
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
}
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec(v___x_841_);
v___x_851_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5, &l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5);
v___x_852_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(v___x_851_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
return v___x_852_;
}
}
v_resetjp_866_:
{
lean_object* v___x_869_; uint8_t v___x_870_; lean_object* v___x_872_; 
v___x_869_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_809_);
v___x_870_ = 0;
if (v_isShared_868_ == 0)
{
v___x_872_ = v___x_867_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_timeout_853_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_maxSteps_863_);
lean_ctor_set_uint8(v_reuseFailAlloc_951_, sizeof(void*)*2 + 1, v_binaryProofs_855_);
lean_ctor_set_uint8(v_reuseFailAlloc_951_, sizeof(void*)*2 + 2, v_acNf_856_);
lean_ctor_set_uint8(v_reuseFailAlloc_951_, sizeof(void*)*2 + 3, v_andFlattening_857_);
lean_ctor_set_uint8(v_reuseFailAlloc_951_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_858_);
lean_ctor_set_uint8(v_reuseFailAlloc_951_, sizeof(void*)*2 + 5, v_structures_859_);
lean_ctor_set_uint8(v_reuseFailAlloc_951_, sizeof(void*)*2 + 6, v_fixedInt_860_);
lean_ctor_set_uint8(v_reuseFailAlloc_951_, sizeof(void*)*2 + 7, v_enums_861_);
lean_ctor_set_uint8(v_reuseFailAlloc_951_, sizeof(void*)*2 + 8, v_graphviz_862_);
lean_ctor_set_uint8(v_reuseFailAlloc_951_, sizeof(void*)*2 + 9, v_shortCircuit_864_);
lean_ctor_set_uint8(v_reuseFailAlloc_951_, sizeof(void*)*2 + 10, v_solverMode_865_);
v___x_872_ = v_reuseFailAlloc_951_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_874_; 
lean_ctor_set_uint8(v___x_872_, sizeof(void*)*2, v___x_870_);
lean_inc_ref(v_lratPath_825_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 5, v___x_872_);
v___x_874_ = v___x_829_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_exprDef_821_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_certDef_822_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_reflectionDef_823_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_solver_824_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_lratPath_825_);
lean_ctor_set(v_reuseFailAlloc_950_, 5, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_950_, 6, v_restrictedTypes_827_);
v___x_874_ = v_reuseFailAlloc_950_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed), 12, 2);
lean_closure_set(v___x_875_, 0, v_target_809_);
lean_closure_set(v___x_875_, 1, v___x_874_);
v___x_876_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v___x_869_, v___x_875_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_941_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_941_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_941_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_941_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
if (lean_obj_tag(v_a_877_) == 0)
{
lean_object* v___x_881_; lean_object* v___x_883_; 
lean_dec_ref(v_lratPath_825_);
v___x_881_ = lean_box(0);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_881_);
v___x_883_ = v___x_879_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
else
{
lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_939_; 
lean_del_object(v___x_879_);
v_isSharedCheck_939_ = !lean_is_exclusive(v_a_877_);
if (v_isSharedCheck_939_ == 0)
{
lean_object* v_unused_940_; 
v_unused_940_ = lean_ctor_get(v_a_877_, 0);
lean_dec(v_unused_940_);
v___x_886_ = v_a_877_;
v_isShared_887_ = v_isSharedCheck_939_;
goto v_resetjp_885_;
}
else
{
lean_dec(v_a_877_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_939_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
if (v_trimProofs_854_ == 0)
{
lean_del_object(v___x_886_);
v___y_832_ = v_a_811_;
v___y_833_ = v_a_812_;
v___y_834_ = v_a_813_;
v___y_835_ = v_a_814_;
v___y_836_ = v_a_815_;
v___y_837_ = v_a_816_;
v___y_838_ = v_a_817_;
v___y_839_ = v_a_818_;
v___y_840_ = v_a_819_;
goto v___jp_831_;
}
else
{
lean_object* v___x_888_; 
v___x_888_ = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(v_lratPath_825_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref_known(v___x_888_, 1);
v___x_890_ = l_Lean_Meta_Tactic_BVDecide_LRAT_trim(v_a_889_);
lean_dec(v_a_889_);
v___x_891_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v___x_890_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_893_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_892_);
lean_dec_ref_known(v___x_891_, 1);
v___x_893_ = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(v_lratPath_825_, v_a_892_, v_binaryProofs_855_);
lean_dec(v_a_892_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_dec_ref_known(v___x_893_, 1);
lean_del_object(v___x_886_);
v___y_832_ = v_a_811_;
v___y_833_ = v_a_812_;
v___y_834_ = v_a_813_;
v___y_835_ = v_a_814_;
v___y_836_ = v_a_815_;
v___y_837_ = v_a_816_;
v___y_838_ = v_a_817_;
v___y_839_ = v_a_818_;
v___y_840_ = v_a_819_;
goto v___jp_831_;
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_908_; 
lean_dec_ref(v_lratPath_825_);
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_908_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_908_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_908_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_ref_898_; lean_object* v___x_899_; lean_object* v___x_901_; 
v_ref_898_ = lean_ctor_get(v_a_818_, 2);
v___x_899_ = lean_io_error_to_string(v_a_894_);
if (v_isShared_887_ == 0)
{
lean_ctor_set_tag(v___x_886_, 3);
lean_ctor_set(v___x_886_, 0, v___x_899_);
v___x_901_ = v___x_886_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_899_);
v___x_901_ = v_reuseFailAlloc_907_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_902_ = l_Lean_MessageData_ofFormat(v___x_901_);
lean_inc(v_ref_898_);
v___x_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_903_, 0, v_ref_898_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_903_);
v___x_905_ = v___x_896_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_923_; 
lean_dec_ref(v_lratPath_825_);
v_a_909_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_923_ == 0)
{
v___x_911_ = v___x_891_;
v_isShared_912_ = v_isSharedCheck_923_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_891_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_923_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v_ref_913_; lean_object* v___x_914_; lean_object* v___x_916_; 
v_ref_913_ = lean_ctor_get(v_a_818_, 2);
v___x_914_ = lean_io_error_to_string(v_a_909_);
if (v_isShared_887_ == 0)
{
lean_ctor_set_tag(v___x_886_, 3);
lean_ctor_set(v___x_886_, 0, v___x_914_);
v___x_916_ = v___x_886_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_914_);
v___x_916_ = v_reuseFailAlloc_922_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_917_ = l_Lean_MessageData_ofFormat(v___x_916_);
lean_inc(v_ref_913_);
v___x_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_918_, 0, v_ref_913_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_918_);
v___x_920_ = v___x_911_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_938_; 
lean_dec_ref(v_lratPath_825_);
v_a_924_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_938_ == 0)
{
v___x_926_ = v___x_888_;
v_isShared_927_ = v_isSharedCheck_938_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_888_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_938_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v_ref_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v_ref_928_ = lean_ctor_get(v_a_818_, 2);
v___x_929_ = lean_io_error_to_string(v_a_924_);
if (v_isShared_887_ == 0)
{
lean_ctor_set_tag(v___x_886_, 3);
lean_ctor_set(v___x_886_, 0, v___x_929_);
v___x_931_ = v___x_886_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_937_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_932_ = l_Lean_MessageData_ofFormat(v___x_931_);
lean_inc(v_ref_928_);
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v_ref_928_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_933_);
v___x_935_ = v___x_926_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
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
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec_ref(v_lratPath_825_);
v_a_942_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_876_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_876_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___boxed(lean_object* v_target_954_, lean_object* v_ctx_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(v_target_954_, v_ctx_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0(lean_object* v_00_u03b1_967_, lean_object* v_msg_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(v_msg_968_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___boxed(lean_object* v_00_u03b1_980_, lean_object* v_msg_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0(v_00_u03b1_980_, v_msg_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
return v_res_992_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = lean_box(0);
v___x_994_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v___x_993_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg(){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0);
v___x_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___boxed(lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0(lean_object* v_00_u03b1_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___boxed(lean_object* v_00_u03b1_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0(v_00_u03b1_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(lean_object* v_snd_1023_, lean_object* v___y_1024_, lean_object* v_a_x3f_1025_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_io_remove_file(v_snd_1023_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1048_; 
v_a_1036_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1038_ = v___x_1027_;
v_isShared_1039_ = v_isSharedCheck_1048_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1027_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1048_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v_ref_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
v_ref_1040_ = lean_ctor_get(v___y_1024_, 2);
v___x_1041_ = lean_io_error_to_string(v_a_1036_);
v___x_1042_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
v___x_1043_ = l_Lean_MessageData_ofFormat(v___x_1042_);
lean_inc(v_ref_1040_);
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v_ref_1040_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v___x_1044_);
v___x_1046_ = v___x_1038_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0___boxed(lean_object* v_snd_1049_, lean_object* v___y_1050_, lean_object* v_a_x3f_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_1049_, v___y_1050_, v_a_x3f_1051_);
lean_dec(v_a_x3f_1051_);
lean_dec_ref(v___y_1050_);
lean_dec_ref(v_snd_1049_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(lean_object* v_f_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v_fst_1066_; lean_object* v_snd_1067_; lean_object* v_r_1068_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1064_, 1);
v_fst_1066_ = lean_ctor_get(v_a_1065_, 0);
lean_inc(v_fst_1066_);
v_snd_1067_ = lean_ctor_get(v_a_1065_, 1);
lean_inc_n(v_snd_1067_, 2);
lean_dec(v_a_1065_);
lean_inc(v___y_1062_);
lean_inc_ref(v___y_1061_);
lean_inc(v___y_1060_);
lean_inc_ref(v___y_1059_);
lean_inc(v___y_1058_);
lean_inc_ref(v___y_1057_);
lean_inc(v___y_1056_);
lean_inc_ref(v___y_1055_);
v_r_1068_ = lean_apply_11(v_f_1054_, v_fst_1066_, v_snd_1067_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, lean_box(0));
if (lean_obj_tag(v_r_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1093_; 
v_a_1069_ = lean_ctor_get(v_r_1068_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_r_1068_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1071_ = v_r_1068_;
v_isShared_1072_ = v_isSharedCheck_1093_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v_r_1068_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1093_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
lean_inc(v_a_1069_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set_tag(v___x_1071_, 1);
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_1067_, v___y_1061_, v___x_1074_);
lean_dec_ref(v___x_1074_);
lean_dec(v_snd_1067_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; 
v_unused_1083_ = lean_ctor_get(v___x_1075_, 0);
lean_dec(v_unused_1083_);
v___x_1077_ = v___x_1075_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_dec(v___x_1075_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v_a_1069_);
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1069_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec(v_a_1069_);
v_a_1084_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1075_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1075_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v_a_1094_ = lean_ctor_get(v_r_1068_, 0);
lean_inc(v_a_1094_);
lean_dec_ref_known(v_r_1068_, 1);
v___x_1095_ = lean_box(0);
v___x_1096_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_1067_, v___y_1061_, v___x_1095_);
lean_dec(v_snd_1067_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1103_ == 0)
{
lean_object* v_unused_1104_; 
v_unused_1104_ = lean_ctor_get(v___x_1096_, 0);
lean_dec(v_unused_1104_);
v___x_1098_ = v___x_1096_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_dec(v___x_1096_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
lean_ctor_set_tag(v___x_1098_, 1);
lean_ctor_set(v___x_1098_, 0, v_a_1094_);
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1094_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec(v_a_1094_);
v_a_1105_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1096_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1096_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1125_; 
lean_dec_ref(v_f_1054_);
v_a_1113_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1115_ = v___x_1064_;
v_isShared_1116_ = v_isSharedCheck_1125_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1064_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1125_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v_ref_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1123_; 
v_ref_1117_ = lean_ctor_get(v___y_1061_, 2);
v___x_1118_ = lean_io_error_to_string(v_a_1113_);
v___x_1119_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
v___x_1120_ = l_Lean_MessageData_ofFormat(v___x_1119_);
lean_inc(v_ref_1117_);
v___x_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1121_, 0, v_ref_1117_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1121_);
v___x_1123_ = v___x_1115_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___boxed(lean_object* v_f_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(v_f_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1(lean_object* v_00_u03b1_1137_, lean_object* v_f_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(v_f_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___boxed(lean_object* v_00_u03b1_1149_, lean_object* v_f_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1(v_00_u03b1_1149_, v_f_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0(uint8_t v___x_1161_, uint8_t v___x_1162_, lean_object* v___x_1163_, lean_object* v___x_1164_, lean_object* v_a_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1167_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1176_);
lean_dec_ref_known(v___x_1175_, 1);
v___x_1177_ = lean_unsigned_to_nat(9u);
v___x_1178_ = lean_unsigned_to_nat(5u);
v___x_1179_ = lean_unsigned_to_nat(8u);
v___x_1180_ = lean_unsigned_to_nat(1000u);
v___x_1181_ = lean_unsigned_to_nat(1024u);
v___x_1182_ = lean_unsigned_to_nat(10000u);
v___x_1183_ = lean_unsigned_to_nat(1048576u);
v___x_1184_ = lean_unsigned_to_nat(50u);
v___x_1185_ = lean_box(0);
v___x_1186_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_1186_, 0, v___x_1177_);
lean_ctor_set(v___x_1186_, 1, v___x_1178_);
lean_ctor_set(v___x_1186_, 2, v___x_1179_);
lean_ctor_set(v___x_1186_, 3, v___x_1179_);
lean_ctor_set(v___x_1186_, 4, v___x_1180_);
lean_ctor_set(v___x_1186_, 5, v___x_1180_);
lean_ctor_set(v___x_1186_, 6, v___x_1163_);
lean_ctor_set(v___x_1186_, 7, v___x_1181_);
lean_ctor_set(v___x_1186_, 8, v___x_1182_);
lean_ctor_set(v___x_1186_, 9, v___x_1180_);
lean_ctor_set(v___x_1186_, 10, v___x_1183_);
lean_ctor_set(v___x_1186_, 11, v___x_1164_);
lean_ctor_set(v___x_1186_, 12, v___x_1184_);
lean_ctor_set(v___x_1186_, 13, v___x_1185_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14, v___x_1161_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 1, v___x_1161_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 2, v___x_1161_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 3, v___x_1161_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 4, v___x_1161_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 5, v___x_1162_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 6, v___x_1162_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 7, v___x_1162_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 8, v___x_1161_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 9, v___x_1161_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 10, v___x_1162_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 11, v___x_1161_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 12, v___x_1162_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 13, v___x_1162_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 14, v___x_1162_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 15, v___x_1162_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 16, v___x_1162_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 17, v___x_1161_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 18, v___x_1162_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 19, v___x_1162_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 20, v___x_1162_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 21, v___x_1162_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 22, v___x_1162_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 23, v___x_1162_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 24, v___x_1162_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 25, v___x_1162_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 26, v___x_1162_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 27, v___x_1162_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 28, v___x_1162_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 29, v___x_1162_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 30, v___x_1161_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 31, v___x_1162_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*14 + 32, v___x_1162_);
v___x_1187_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_1186_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref_known(v___x_1187_, 1);
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v_a_1176_);
v___x_1190_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed), 12, 2);
lean_closure_set(v___x_1190_, 0, v___x_1189_);
lean_closure_set(v___x_1190_, 1, v_a_1165_);
v___x_1191_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___x_1190_, v_a_1188_, v___x_1185_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
lean_dec_ref_known(v___x_1191_, 1);
v___x_1192_ = lean_box(0);
v___x_1193_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1192_, v___y_1167_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1201_; 
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; 
v_unused_1202_ = lean_ctor_get(v___x_1193_, 0);
lean_dec(v_unused_1202_);
v___x_1195_ = v___x_1193_;
v_isShared_1196_ = v_isSharedCheck_1201_;
goto v_resetjp_1194_;
}
else
{
lean_dec(v___x_1193_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1201_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1197_ = lean_box(0);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1197_);
v___x_1199_ = v___x_1195_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
else
{
return v___x_1193_;
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
v_a_1203_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1191_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1191_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
else
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_dec(v_a_1176_);
lean_dec_ref(v_a_1165_);
v_a_1211_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1187_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1187_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_dec_ref(v_a_1165_);
lean_dec(v___x_1164_);
lean_dec(v___x_1163_);
v_a_1219_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1175_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1175_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0___boxed(lean_object* v___x_1227_, lean_object* v___x_1228_, lean_object* v___x_1229_, lean_object* v___x_1230_, lean_object* v_a_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
uint8_t v___x_5633__boxed_1241_; uint8_t v___x_5634__boxed_1242_; lean_object* v_res_1243_; 
v___x_5633__boxed_1241_ = lean_unbox(v___x_1227_);
v___x_5634__boxed_1242_ = lean_unbox(v___x_1228_);
v_res_1243_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0(v___x_5633__boxed_1241_, v___x_5634__boxed_1242_, v___x_1229_, v___x_1230_, v_a_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1(lean_object* v_a_1244_, lean_object* v_a_1245_, uint8_t v___x_1246_, uint8_t v___x_1247_, lean_object* v___x_1248_, lean_object* v___x_1249_, lean_object* v_x_1250_, lean_object* v_lratFile_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new(v_lratFile_1251_, v_a_1244_, v_a_1245_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___f_1265_; lean_object* v___x_1266_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___x_1261_, 1);
v___x_1263_ = lean_box(v___x_1246_);
v___x_1264_ = lean_box(v___x_1247_);
v___f_1265_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0___boxed), 14, 5);
lean_closure_set(v___f_1265_, 0, v___x_1263_);
lean_closure_set(v___f_1265_, 1, v___x_1264_);
lean_closure_set(v___f_1265_, 2, v___x_1248_);
lean_closure_set(v___f_1265_, 3, v___x_1249_);
lean_closure_set(v___f_1265_, 4, v_a_1262_);
v___x_1266_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1265_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
return v___x_1266_;
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec(v___x_1249_);
lean_dec(v___x_1248_);
v_a_1267_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1261_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1261_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1___boxed(lean_object** _args){
lean_object* v_a_1275_ = _args[0];
lean_object* v_a_1276_ = _args[1];
lean_object* v___x_1277_ = _args[2];
lean_object* v___x_1278_ = _args[3];
lean_object* v___x_1279_ = _args[4];
lean_object* v___x_1280_ = _args[5];
lean_object* v_x_1281_ = _args[6];
lean_object* v_lratFile_1282_ = _args[7];
lean_object* v___y_1283_ = _args[8];
lean_object* v___y_1284_ = _args[9];
lean_object* v___y_1285_ = _args[10];
lean_object* v___y_1286_ = _args[11];
lean_object* v___y_1287_ = _args[12];
lean_object* v___y_1288_ = _args[13];
lean_object* v___y_1289_ = _args[14];
lean_object* v___y_1290_ = _args[15];
lean_object* v___y_1291_ = _args[16];
_start:
{
uint8_t v___x_5784__boxed_1292_; uint8_t v___x_5785__boxed_1293_; lean_object* v_res_1294_; 
v___x_5784__boxed_1292_ = lean_unbox(v___x_1277_);
v___x_5785__boxed_1293_ = lean_unbox(v___x_1278_);
v_res_1294_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1(v_a_1275_, v_a_1276_, v___x_5784__boxed_1292_, v___x_5785__boxed_1293_, v___x_1279_, v___x_1280_, v_x_1281_, v_lratFile_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v_x_1281_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide(lean_object* v_x_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3));
lean_inc(v_x_1315_);
v___x_1326_ = l_Lean_Syntax_isOfKind(v_x_1315_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; 
lean_dec(v_x_1315_);
v___x_1327_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1327_;
}
else
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; lean_object* v_types_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; 
v___x_1328_ = lean_unsigned_to_nat(1u);
v___x_1329_ = l_Lean_Syntax_getArg(v_x_1315_, v___x_1328_);
v___x_1330_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_1329_);
v___x_1331_ = l_Lean_Syntax_isOfKind(v___x_1329_, v___x_1330_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1372_; 
lean_dec(v___x_1329_);
lean_dec(v_x_1315_);
v___x_1372_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1372_;
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1373_ = lean_unsigned_to_nat(2u);
v___x_1374_ = l_Lean_Syntax_getArg(v_x_1315_, v___x_1373_);
lean_dec(v_x_1315_);
v___x_1375_ = l_Lean_Syntax_isNone(v___x_1374_);
if (v___x_1375_ == 0)
{
uint8_t v___x_1376_; 
lean_inc(v___x_1374_);
v___x_1376_ = l_Lean_Syntax_matchesNull(v___x_1374_, v___x_1328_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; 
lean_dec(v___x_1374_);
lean_dec(v___x_1329_);
v___x_1377_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1377_;
}
else
{
lean_object* v___x_1378_; lean_object* v_types_1379_; 
v___x_1378_ = lean_unsigned_to_nat(0u);
v_types_1379_ = l_Lean_Syntax_getArg(v___x_1374_, v___x_1378_);
lean_dec(v___x_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1382_; uint8_t v___x_1383_; 
v___x_1382_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_types_1379_);
v___x_1383_ = l_Lean_Syntax_isOfKind(v_types_1379_, v___x_1382_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; 
lean_dec(v_types_1379_);
lean_dec(v___x_1329_);
v___x_1384_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1384_;
}
else
{
goto v___jp_1380_;
}
}
else
{
goto v___jp_1380_;
}
v___jp_1380_:
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1381_, 0, v_types_1379_);
v_types_1333_ = v___x_1381_;
v___y_1334_ = v_a_1316_;
v___y_1335_ = v_a_1317_;
v___y_1336_ = v_a_1318_;
v___y_1337_ = v_a_1319_;
v___y_1338_ = v_a_1320_;
v___y_1339_ = v_a_1321_;
v___y_1340_ = v_a_1322_;
v___y_1341_ = v_a_1323_;
goto v___jp_1332_;
}
}
}
else
{
lean_object* v___x_1385_; 
lean_dec(v___x_1374_);
v___x_1385_ = lean_box(0);
v_types_1333_ = v___x_1385_;
v___y_1334_ = v_a_1316_;
v___y_1335_ = v_a_1317_;
v___y_1336_ = v_a_1318_;
v___y_1337_ = v_a_1319_;
v___y_1338_ = v_a_1320_;
v___y_1339_ = v_a_1321_;
v___y_1340_ = v_a_1322_;
v___y_1341_ = v_a_1323_;
goto v___jp_1332_;
}
}
v___jp_1332_:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v___x_1343_; uint8_t v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
lean_dec_ref_known(v___x_1342_, 1);
v___x_1343_ = lean_unsigned_to_nat(10u);
v___x_1344_ = 0;
v___x_1345_ = lean_unsigned_to_nat(100000u);
v___x_1346_ = 0;
v___x_1347_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_1347_, 0, v___x_1343_);
lean_ctor_set(v___x_1347_, 1, v___x_1345_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*2, v___x_1331_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*2 + 1, v___x_1331_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*2 + 2, v___x_1344_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*2 + 3, v___x_1331_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*2 + 4, v___x_1331_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*2 + 5, v___x_1331_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*2 + 6, v___x_1331_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*2 + 7, v___x_1331_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*2 + 8, v___x_1344_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*2 + 9, v___x_1344_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*2 + 10, v___x_1346_);
v___x_1348_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_1329_, v___x_1347_, v___x_1331_, v___y_1334_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1350_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
lean_dec_ref_known(v___x_1348_, 1);
v___x_1350_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_types_1333_, v_a_1349_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___f_1354_; lean_object* v___x_1355_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1350_, 1);
v___x_1352_ = lean_box(v___x_1344_);
v___x_1353_ = lean_box(v___x_1331_);
v___f_1354_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1___boxed), 17, 6);
lean_closure_set(v___f_1354_, 0, v_a_1349_);
lean_closure_set(v___f_1354_, 1, v_a_1351_);
lean_closure_set(v___f_1354_, 2, v___x_1352_);
lean_closure_set(v___f_1354_, 3, v___x_1353_);
lean_closure_set(v___f_1354_, 4, v___x_1345_);
lean_closure_set(v___f_1354_, 5, v___x_1343_);
v___x_1355_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(v___f_1354_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
return v___x_1355_;
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_dec(v_a_1349_);
v_a_1356_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1350_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1350_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec(v_types_1333_);
v_a_1364_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1348_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1348_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
else
{
lean_dec(v_types_1333_);
lean_dec(v___x_1329_);
return v___x_1342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___boxed(lean_object* v_x_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide(v_x_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
lean_dec(v_a_1392_);
lean_dec_ref(v_a_1391_);
lean_dec(v_a_1390_);
lean_dec_ref(v_a_1389_);
lean_dec(v_a_1388_);
lean_dec_ref(v_a_1387_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1(){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1406_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1407_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3));
v___x_1408_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2));
v___x_1409_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___boxed), 10, 0);
v___x_1410_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1406_, v___x_1407_, v___x_1408_, v___x_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___boxed(lean_object* v_a_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1();
return v_res_1412_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Array_mkArray0(lean_box(0));
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0(lean_object* v___x_1425_, lean_object* v_a_1426_, uint8_t v___x_1427_, lean_object* v___x_1428_, lean_object* v___x_1429_, lean_object* v___x_1430_, lean_object* v___x_1431_, lean_object* v_tk_1432_, lean_object* v_typesStx_1433_, lean_object* v___x_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(v___x_1425_, v_a_1426_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
lean_dec_ref_known(v___x_1445_, 1);
if (lean_obj_tag(v_a_1446_) == 0)
{
lean_object* v_ref_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___y_1457_; 
v_ref_1447_ = lean_ctor_get(v___y_1442_, 2);
v___x_1448_ = l_Lean_SourceInfo_fromRef(v_ref_1447_, v___x_1427_);
v___x_1449_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__1));
v___x_1450_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__2));
v___x_1451_ = l_Lean_Name_mkStr4(v___x_1428_, v___x_1429_, v___x_1430_, v___x_1450_);
v___x_1452_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3));
lean_inc(v___x_1448_);
v___x_1453_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1448_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
v___x_1454_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5));
v___x_1455_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6);
if (lean_obj_tag(v_typesStx_1433_) == 1)
{
lean_object* v_val_1469_; lean_object* v___x_1470_; 
v_val_1469_ = lean_ctor_get(v_typesStx_1433_, 0);
lean_inc(v_val_1469_);
lean_dec_ref_known(v_typesStx_1433_, 1);
v___x_1470_ = l_Array_mkArray1___redArg(v_val_1469_);
v___y_1457_ = v___x_1470_;
goto v___jp_1456_;
}
else
{
lean_object* v___x_1471_; 
lean_dec(v_typesStx_1433_);
v___x_1471_ = lean_mk_empty_array_with_capacity(v___x_1434_);
v___y_1457_ = v___x_1471_;
goto v___jp_1456_;
}
v___jp_1456_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1458_ = l_Array_append___redArg(v___x_1455_, v___y_1457_);
lean_dec_ref(v___y_1457_);
lean_inc(v___x_1448_);
v___x_1459_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1448_);
lean_ctor_set(v___x_1459_, 1, v___x_1454_);
lean_ctor_set(v___x_1459_, 2, v___x_1458_);
v___x_1460_ = l_Lean_Syntax_node3(v___x_1448_, v___x_1451_, v___x_1453_, v___x_1431_, v___x_1459_);
v___x_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1449_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
v___x_1462_ = lean_box(0);
v___x_1463_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1461_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
lean_ctor_set(v___x_1463_, 2, v___x_1462_);
lean_ctor_set(v___x_1463_, 3, v___x_1462_);
lean_ctor_set(v___x_1463_, 4, v___x_1462_);
lean_ctor_set(v___x_1463_, 5, v___x_1462_);
lean_inc(v_ref_1447_);
v___x_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1464_, 0, v_ref_1447_);
v___x_1465_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__7));
v___x_1466_ = 4;
v___x_1467_ = l_Lean_MessageData_nil;
v___x_1468_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1432_, v___x_1463_, v___x_1464_, v___x_1465_, v___x_1462_, v___x_1466_, v___x_1467_, v___y_1442_, v___y_1443_);
return v___x_1468_;
}
}
else
{
lean_object* v_path_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1505_; 
v_path_1472_ = lean_ctor_get(v_a_1446_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_a_1446_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1474_ = v_a_1446_;
v_isShared_1475_ = v_isSharedCheck_1505_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_path_1472_);
lean_dec(v_a_1446_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1505_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v_ref_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___y_1486_; 
v_ref_1476_ = lean_ctor_get(v___y_1442_, 2);
v___x_1477_ = l_Lean_SourceInfo_fromRef(v_ref_1476_, v___x_1427_);
v___x_1478_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__1));
v___x_1479_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__8));
v___x_1480_ = l_Lean_Name_mkStr4(v___x_1428_, v___x_1429_, v___x_1430_, v___x_1479_);
v___x_1481_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__9));
lean_inc(v___x_1477_);
v___x_1482_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1477_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v___x_1483_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5));
v___x_1484_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6);
if (lean_obj_tag(v_typesStx_1433_) == 1)
{
lean_object* v_val_1502_; lean_object* v___x_1503_; 
v_val_1502_ = lean_ctor_get(v_typesStx_1433_, 0);
lean_inc(v_val_1502_);
lean_dec_ref_known(v_typesStx_1433_, 1);
v___x_1503_ = l_Array_mkArray1___redArg(v_val_1502_);
v___y_1486_ = v___x_1503_;
goto v___jp_1485_;
}
else
{
lean_object* v___x_1504_; 
lean_dec(v_typesStx_1433_);
v___x_1504_ = lean_mk_empty_array_with_capacity(v___x_1434_);
v___y_1486_ = v___x_1504_;
goto v___jp_1485_;
}
v___jp_1485_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1487_ = l_Array_append___redArg(v___x_1484_, v___y_1486_);
lean_dec_ref(v___y_1486_);
lean_inc(v___x_1477_);
v___x_1488_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1477_);
lean_ctor_set(v___x_1488_, 1, v___x_1483_);
lean_ctor_set(v___x_1488_, 2, v___x_1487_);
v___x_1489_ = lean_box(2);
v___x_1490_ = l_Lean_Syntax_mkStrLit(v_path_1472_, v___x_1489_);
v___x_1491_ = l_Lean_Syntax_node4(v___x_1477_, v___x_1480_, v___x_1482_, v___x_1431_, v___x_1488_, v___x_1490_);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1478_);
lean_ctor_set(v___x_1492_, 1, v___x_1491_);
v___x_1493_ = lean_box(0);
v___x_1494_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1492_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
lean_ctor_set(v___x_1494_, 2, v___x_1493_);
lean_ctor_set(v___x_1494_, 3, v___x_1493_);
lean_ctor_set(v___x_1494_, 4, v___x_1493_);
lean_ctor_set(v___x_1494_, 5, v___x_1493_);
lean_inc(v_ref_1476_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 0, v_ref_1476_);
v___x_1496_ = v___x_1474_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_ref_1476_);
v___x_1496_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1497_; uint8_t v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1497_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__7));
v___x_1498_ = 4;
v___x_1499_ = l_Lean_MessageData_nil;
v___x_1500_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1432_, v___x_1494_, v___x_1496_, v___x_1497_, v___x_1493_, v___x_1498_, v___x_1499_, v___y_1442_, v___y_1443_);
return v___x_1500_;
}
}
}
}
}
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
lean_dec(v_typesStx_1433_);
lean_dec(v_tk_1432_);
lean_dec(v___x_1431_);
lean_dec_ref(v___x_1430_);
lean_dec_ref(v___x_1429_);
lean_dec_ref(v___x_1428_);
v_a_1506_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1445_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1445_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___boxed(lean_object** _args){
lean_object* v___x_1514_ = _args[0];
lean_object* v_a_1515_ = _args[1];
lean_object* v___x_1516_ = _args[2];
lean_object* v___x_1517_ = _args[3];
lean_object* v___x_1518_ = _args[4];
lean_object* v___x_1519_ = _args[5];
lean_object* v___x_1520_ = _args[6];
lean_object* v_tk_1521_ = _args[7];
lean_object* v_typesStx_1522_ = _args[8];
lean_object* v___x_1523_ = _args[9];
lean_object* v___y_1524_ = _args[10];
lean_object* v___y_1525_ = _args[11];
lean_object* v___y_1526_ = _args[12];
lean_object* v___y_1527_ = _args[13];
lean_object* v___y_1528_ = _args[14];
lean_object* v___y_1529_ = _args[15];
lean_object* v___y_1530_ = _args[16];
lean_object* v___y_1531_ = _args[17];
lean_object* v___y_1532_ = _args[18];
lean_object* v___y_1533_ = _args[19];
_start:
{
uint8_t v___x_20506__boxed_1534_; lean_object* v_res_1535_; 
v___x_20506__boxed_1534_ = lean_unbox(v___x_1516_);
v_res_1535_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0(v___x_1514_, v_a_1515_, v___x_20506__boxed_1534_, v___x_1517_, v___x_1518_, v___x_1519_, v___x_1520_, v_tk_1521_, v_typesStx_1522_, v___x_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec(v___x_1523_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic(lean_object* v_x_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1552_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0));
v___x_1553_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1));
v___x_1554_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1));
v___x_1555_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__1));
lean_inc(v_x_1542_);
v___x_1556_ = l_Lean_Syntax_isOfKind(v_x_1542_, v___x_1555_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; 
lean_dec(v_x_1542_);
v___x_1557_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1557_;
}
else
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; 
v___x_1558_ = lean_unsigned_to_nat(1u);
v___x_1559_ = l_Lean_Syntax_getArg(v_x_1542_, v___x_1558_);
v___x_1560_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_1559_);
v___x_1561_ = l_Lean_Syntax_isOfKind(v___x_1559_, v___x_1560_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; 
lean_dec(v___x_1559_);
lean_dec(v_x_1542_);
v___x_1562_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1562_;
}
else
{
lean_object* v___x_1563_; lean_object* v_tk_1564_; lean_object* v_typesStx_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___x_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; 
v___x_1563_ = lean_unsigned_to_nat(0u);
v_tk_1564_ = l_Lean_Syntax_getArg(v_x_1542_, v___x_1563_);
v___x_1652_ = lean_unsigned_to_nat(2u);
v___x_1653_ = l_Lean_Syntax_getArg(v_x_1542_, v___x_1652_);
lean_dec(v_x_1542_);
v___x_1654_ = l_Lean_Syntax_isNone(v___x_1653_);
if (v___x_1654_ == 0)
{
uint8_t v___x_1655_; 
lean_inc(v___x_1653_);
v___x_1655_ = l_Lean_Syntax_matchesNull(v___x_1653_, v___x_1558_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; 
lean_dec(v___x_1653_);
lean_dec(v_tk_1564_);
lean_dec(v___x_1559_);
v___x_1656_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1656_;
}
else
{
lean_object* v_typesStx_1657_; 
v_typesStx_1657_ = l_Lean_Syntax_getArg(v___x_1653_, v___x_1563_);
lean_dec(v___x_1653_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1660_; uint8_t v___x_1661_; 
v___x_1660_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_typesStx_1657_);
v___x_1661_ = l_Lean_Syntax_isOfKind(v_typesStx_1657_, v___x_1660_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; 
lean_dec(v_typesStx_1657_);
lean_dec(v_tk_1564_);
lean_dec(v___x_1559_);
v___x_1662_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1662_;
}
else
{
goto v___jp_1658_;
}
}
else
{
goto v___jp_1658_;
}
v___jp_1658_:
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1659_, 0, v_typesStx_1657_);
v_typesStx_1566_ = v___x_1659_;
v___y_1567_ = v_a_1543_;
v___y_1568_ = v_a_1544_;
v___y_1569_ = v_a_1545_;
v___y_1570_ = v_a_1546_;
v___y_1571_ = v_a_1547_;
v___y_1572_ = v_a_1548_;
v___y_1573_ = v_a_1549_;
v___y_1574_ = v_a_1550_;
goto v___jp_1565_;
}
}
}
else
{
lean_object* v___x_1663_; 
lean_dec(v___x_1653_);
v___x_1663_ = lean_box(0);
v_typesStx_1566_ = v___x_1663_;
v___y_1567_ = v_a_1543_;
v___y_1568_ = v_a_1544_;
v___y_1569_ = v_a_1545_;
v___y_1570_ = v_a_1546_;
v___y_1571_ = v_a_1547_;
v___y_1572_ = v_a_1548_;
v___y_1573_ = v_a_1549_;
v___y_1574_ = v_a_1550_;
goto v___jp_1565_;
}
v___jp_1565_:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1573_, v___y_1574_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1650_; 
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1650_ == 0)
{
lean_object* v_unused_1651_; 
v_unused_1651_ = lean_ctor_get(v___x_1575_, 0);
lean_dec(v_unused_1651_);
v___x_1577_ = v___x_1575_;
v_isShared_1578_ = v_isSharedCheck_1650_;
goto v_resetjp_1576_;
}
else
{
lean_dec(v___x_1575_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1650_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; uint8_t v___x_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1579_ = lean_unsigned_to_nat(10u);
v___x_1580_ = 0;
v___x_1581_ = lean_unsigned_to_nat(100000u);
v___x_1582_ = 0;
v___x_1583_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_1583_, 0, v___x_1579_);
lean_ctor_set(v___x_1583_, 1, v___x_1581_);
lean_ctor_set_uint8(v___x_1583_, sizeof(void*)*2, v___x_1561_);
lean_ctor_set_uint8(v___x_1583_, sizeof(void*)*2 + 1, v___x_1561_);
lean_ctor_set_uint8(v___x_1583_, sizeof(void*)*2 + 2, v___x_1580_);
lean_ctor_set_uint8(v___x_1583_, sizeof(void*)*2 + 3, v___x_1561_);
lean_ctor_set_uint8(v___x_1583_, sizeof(void*)*2 + 4, v___x_1561_);
lean_ctor_set_uint8(v___x_1583_, sizeof(void*)*2 + 5, v___x_1561_);
lean_ctor_set_uint8(v___x_1583_, sizeof(void*)*2 + 6, v___x_1561_);
lean_ctor_set_uint8(v___x_1583_, sizeof(void*)*2 + 7, v___x_1561_);
lean_ctor_set_uint8(v___x_1583_, sizeof(void*)*2 + 8, v___x_1580_);
lean_ctor_set_uint8(v___x_1583_, sizeof(void*)*2 + 9, v___x_1580_);
lean_ctor_set_uint8(v___x_1583_, sizeof(void*)*2 + 10, v___x_1582_);
lean_inc(v___x_1559_);
v___x_1584_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_1559_, v___x_1583_, v___x_1561_, v___y_1567_, v___y_1573_, v___y_1574_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1586_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
lean_inc(v_typesStx_1566_);
v___x_1586_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_1566_, v_a_1585_, v___y_1573_, v___y_1574_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1588_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1586_, 1);
v___x_1588_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(v_a_1585_, v_a_1587_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1590_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1589_);
lean_dec_ref_known(v___x_1588_, 1);
v___x_1590_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1568_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref_known(v___x_1590_, 1);
v___x_1592_ = lean_unsigned_to_nat(9u);
v___x_1593_ = lean_unsigned_to_nat(5u);
v___x_1594_ = lean_unsigned_to_nat(8u);
v___x_1595_ = lean_unsigned_to_nat(1000u);
v___x_1596_ = lean_unsigned_to_nat(1024u);
v___x_1597_ = lean_unsigned_to_nat(10000u);
v___x_1598_ = lean_unsigned_to_nat(1048576u);
v___x_1599_ = lean_unsigned_to_nat(50u);
v___x_1600_ = lean_box(0);
v___x_1601_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_1601_, 0, v___x_1592_);
lean_ctor_set(v___x_1601_, 1, v___x_1593_);
lean_ctor_set(v___x_1601_, 2, v___x_1594_);
lean_ctor_set(v___x_1601_, 3, v___x_1594_);
lean_ctor_set(v___x_1601_, 4, v___x_1595_);
lean_ctor_set(v___x_1601_, 5, v___x_1595_);
lean_ctor_set(v___x_1601_, 6, v___x_1581_);
lean_ctor_set(v___x_1601_, 7, v___x_1596_);
lean_ctor_set(v___x_1601_, 8, v___x_1597_);
lean_ctor_set(v___x_1601_, 9, v___x_1595_);
lean_ctor_set(v___x_1601_, 10, v___x_1598_);
lean_ctor_set(v___x_1601_, 11, v___x_1579_);
lean_ctor_set(v___x_1601_, 12, v___x_1599_);
lean_ctor_set(v___x_1601_, 13, v___x_1600_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14, v___x_1580_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 1, v___x_1580_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 2, v___x_1580_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 3, v___x_1580_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 4, v___x_1580_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 5, v___x_1561_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 6, v___x_1561_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 7, v___x_1561_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 8, v___x_1580_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 9, v___x_1580_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 10, v___x_1561_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 11, v___x_1580_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 12, v___x_1561_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 13, v___x_1561_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 14, v___x_1561_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 15, v___x_1561_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 16, v___x_1561_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 17, v___x_1580_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 18, v___x_1561_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 19, v___x_1561_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 20, v___x_1561_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 21, v___x_1561_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 22, v___x_1561_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 23, v___x_1561_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 24, v___x_1561_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 25, v___x_1561_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 26, v___x_1561_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 27, v___x_1561_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 28, v___x_1561_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 29, v___x_1561_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 30, v___x_1580_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 31, v___x_1561_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 32, v___x_1561_);
v___x_1602_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_1601_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; lean_object* v___x_1605_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_a_1603_);
lean_dec_ref_known(v___x_1602_, 1);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v_a_1591_);
v___x_1605_ = v___x_1577_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1591_);
v___x_1605_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1606_; lean_object* v___f_1607_; lean_object* v___x_1608_; 
v___x_1606_ = lean_box(v___x_1580_);
v___f_1607_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___boxed), 20, 10);
lean_closure_set(v___f_1607_, 0, v___x_1605_);
lean_closure_set(v___f_1607_, 1, v_a_1589_);
lean_closure_set(v___f_1607_, 2, v___x_1606_);
lean_closure_set(v___f_1607_, 3, v___x_1552_);
lean_closure_set(v___f_1607_, 4, v___x_1553_);
lean_closure_set(v___f_1607_, 5, v___x_1554_);
lean_closure_set(v___f_1607_, 6, v___x_1559_);
lean_closure_set(v___f_1607_, 7, v_tk_1564_);
lean_closure_set(v___f_1607_, 8, v_typesStx_1566_);
lean_closure_set(v___f_1607_, 9, v___x_1563_);
v___x_1608_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___f_1607_, v_a_1603_, v___x_1600_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
return v___x_1608_;
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_dec(v_a_1591_);
lean_dec(v_a_1589_);
lean_del_object(v___x_1577_);
lean_dec(v_typesStx_1566_);
lean_dec(v_tk_1564_);
lean_dec(v___x_1559_);
v_a_1610_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1602_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1602_);
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
lean_dec(v_a_1589_);
lean_del_object(v___x_1577_);
lean_dec(v_typesStx_1566_);
lean_dec(v_tk_1564_);
lean_dec(v___x_1559_);
v_a_1618_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1590_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1590_);
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
lean_del_object(v___x_1577_);
lean_dec(v_typesStx_1566_);
lean_dec(v_tk_1564_);
lean_dec(v___x_1559_);
v_a_1626_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1588_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1588_);
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
lean_dec(v_a_1585_);
lean_del_object(v___x_1577_);
lean_dec(v_typesStx_1566_);
lean_dec(v_tk_1564_);
lean_dec(v___x_1559_);
v_a_1634_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1586_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1586_);
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
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
lean_del_object(v___x_1577_);
lean_dec(v_typesStx_1566_);
lean_dec(v_tk_1564_);
lean_dec(v___x_1559_);
v_a_1642_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1584_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1584_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
}
else
{
lean_dec(v_typesStx_1566_);
lean_dec(v_tk_1564_);
lean_dec(v___x_1559_);
return v___x_1575_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___boxed(lean_object* v_x_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic(v_x_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec(v_a_1668_);
lean_dec_ref(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1(){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1683_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1684_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__1));
v___x_1685_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___closed__1));
v___x_1686_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___boxed), 10, 0);
v___x_1687_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1683_, v___x_1684_, v___x_1685_, v___x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___boxed(lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1();
return v_res_1689_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_1696_, uint8_t v___y_1697_, lean_object* v_x_1698_){
_start:
{
if (lean_obj_tag(v_x_1698_) == 1)
{
lean_object* v_pre_1699_; 
v_pre_1699_ = lean_ctor_get(v_x_1698_, 0);
switch(lean_obj_tag(v_pre_1699_))
{
case 1:
{
lean_object* v_pre_1700_; 
v_pre_1700_ = lean_ctor_get(v_pre_1699_, 0);
switch(lean_obj_tag(v_pre_1700_))
{
case 0:
{
lean_object* v_str_1701_; lean_object* v_str_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; 
v_str_1701_ = lean_ctor_get(v_x_1698_, 1);
v_str_1702_ = lean_ctor_get(v_pre_1699_, 1);
v___x_1703_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__0));
v___x_1704_ = lean_string_dec_eq(v_str_1702_, v___x_1703_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; uint8_t v___x_1706_; 
v___x_1705_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1));
v___x_1706_ = lean_string_dec_eq(v_str_1702_, v___x_1705_);
if (v___x_1706_ == 0)
{
return v___x_1706_;
}
else
{
lean_object* v___x_1707_; uint8_t v___x_1708_; 
v___x_1707_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_1708_ = lean_string_dec_eq(v_str_1701_, v___x_1707_);
if (v___x_1708_ == 0)
{
return v___x_1708_;
}
else
{
return v_suppressElabErrors_1696_;
}
}
}
else
{
lean_object* v___x_1709_; uint8_t v___x_1710_; 
v___x_1709_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_1710_ = lean_string_dec_eq(v_str_1701_, v___x_1709_);
if (v___x_1710_ == 0)
{
return v___x_1710_;
}
else
{
return v_suppressElabErrors_1696_;
}
}
}
case 1:
{
lean_object* v_pre_1711_; 
v_pre_1711_ = lean_ctor_get(v_pre_1700_, 0);
if (lean_obj_tag(v_pre_1711_) == 0)
{
lean_object* v_str_1712_; lean_object* v_str_1713_; lean_object* v_str_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; 
v_str_1712_ = lean_ctor_get(v_x_1698_, 1);
v_str_1713_ = lean_ctor_get(v_pre_1699_, 1);
v_str_1714_ = lean_ctor_get(v_pre_1700_, 1);
v___x_1715_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_1716_ = lean_string_dec_eq(v_str_1714_, v___x_1715_);
if (v___x_1716_ == 0)
{
return v___x_1716_;
}
else
{
lean_object* v___x_1717_; uint8_t v___x_1718_; 
v___x_1717_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_1718_ = lean_string_dec_eq(v_str_1713_, v___x_1717_);
if (v___x_1718_ == 0)
{
return v___x_1718_;
}
else
{
lean_object* v___x_1719_; uint8_t v___x_1720_; 
v___x_1719_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_1720_ = lean_string_dec_eq(v_str_1712_, v___x_1719_);
if (v___x_1720_ == 0)
{
return v___x_1720_;
}
else
{
return v_suppressElabErrors_1696_;
}
}
}
}
else
{
return v___y_1697_;
}
}
default: 
{
return v___y_1697_;
}
}
}
case 0:
{
lean_object* v_str_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; 
v_str_1721_ = lean_ctor_get(v_x_1698_, 1);
v___x_1722_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_1723_ = lean_string_dec_eq(v_str_1721_, v___x_1722_);
if (v___x_1723_ == 0)
{
return v___x_1723_;
}
else
{
return v_suppressElabErrors_1696_;
}
}
default: 
{
return v___y_1697_;
}
}
}
else
{
return v___y_1697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_1724_, lean_object* v___y_1725_, lean_object* v_x_1726_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1727_; uint8_t v___y_7426__boxed_1728_; uint8_t v_res_1729_; lean_object* v_r_1730_; 
v_suppressElabErrors_boxed_1727_ = lean_unbox(v_suppressElabErrors_1724_);
v___y_7426__boxed_1728_ = lean_unbox(v___y_1725_);
v_res_1729_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_1727_, v___y_7426__boxed_1728_, v_x_1726_);
lean_dec(v_x_1726_);
v_r_1730_ = lean_box(v_res_1729_);
return v_r_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(lean_object* v_ref_1732_, lean_object* v_msgData_1733_, uint8_t v_severity_1734_, uint8_t v_isSilent_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v___y_1742_; uint8_t v___y_1743_; lean_object* v___y_1744_; uint8_t v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1779_; uint8_t v___y_1780_; uint8_t v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; uint8_t v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1804_; uint8_t v___y_1805_; uint8_t v___y_1806_; lean_object* v___y_1807_; uint8_t v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1815_; uint8_t v___y_1816_; lean_object* v___y_1817_; uint8_t v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; uint8_t v___y_1821_; uint8_t v___x_1826_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; uint8_t v___y_1831_; uint8_t v___y_1832_; lean_object* v___y_1833_; uint8_t v___y_1834_; uint8_t v___y_1836_; uint8_t v___x_1852_; 
v___x_1826_ = 2;
v___x_1852_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1734_, v___x_1826_);
if (v___x_1852_ == 0)
{
v___y_1836_ = v___x_1852_;
goto v___jp_1835_;
}
else
{
uint8_t v___x_1853_; 
lean_inc_ref(v_msgData_1733_);
v___x_1853_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1733_);
v___y_1836_ = v___x_1853_;
goto v___jp_1835_;
}
v___jp_1741_:
{
lean_object* v___x_1751_; lean_object* v_toCold_1752_; lean_object* v_currNamespace_1753_; lean_object* v_openDecls_1754_; lean_object* v_env_1755_; lean_object* v_nextMacroScope_1756_; lean_object* v_ngen_1757_; lean_object* v_auxDeclNGen_1758_; lean_object* v_traceState_1759_; lean_object* v_cache_1760_; lean_object* v_messages_1761_; lean_object* v_infoState_1762_; lean_object* v_snapshotTasks_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1777_; 
v___x_1751_ = lean_st_ref_take(v___y_1750_);
v_toCold_1752_ = lean_ctor_get(v___y_1749_, 0);
v_currNamespace_1753_ = lean_ctor_get(v_toCold_1752_, 4);
v_openDecls_1754_ = lean_ctor_get(v_toCold_1752_, 5);
v_env_1755_ = lean_ctor_get(v___x_1751_, 0);
v_nextMacroScope_1756_ = lean_ctor_get(v___x_1751_, 1);
v_ngen_1757_ = lean_ctor_get(v___x_1751_, 2);
v_auxDeclNGen_1758_ = lean_ctor_get(v___x_1751_, 3);
v_traceState_1759_ = lean_ctor_get(v___x_1751_, 4);
v_cache_1760_ = lean_ctor_get(v___x_1751_, 5);
v_messages_1761_ = lean_ctor_get(v___x_1751_, 6);
v_infoState_1762_ = lean_ctor_get(v___x_1751_, 7);
v_snapshotTasks_1763_ = lean_ctor_get(v___x_1751_, 8);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1765_ = v___x_1751_;
v_isShared_1766_ = v_isSharedCheck_1777_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_snapshotTasks_1763_);
lean_inc(v_infoState_1762_);
lean_inc(v_messages_1761_);
lean_inc(v_cache_1760_);
lean_inc(v_traceState_1759_);
lean_inc(v_auxDeclNGen_1758_);
lean_inc(v_ngen_1757_);
lean_inc(v_nextMacroScope_1756_);
lean_inc(v_env_1755_);
lean_dec(v___x_1751_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1777_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1772_; 
lean_inc(v_openDecls_1754_);
lean_inc(v_currNamespace_1753_);
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v_currNamespace_1753_);
lean_ctor_set(v___x_1767_, 1, v_openDecls_1754_);
v___x_1768_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
lean_ctor_set(v___x_1768_, 1, v___y_1748_);
lean_inc_ref(v___y_1744_);
lean_inc_ref(v___y_1747_);
v___x_1769_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1769_, 0, v___y_1747_);
lean_ctor_set(v___x_1769_, 1, v___y_1746_);
lean_ctor_set(v___x_1769_, 2, v___y_1742_);
lean_ctor_set(v___x_1769_, 3, v___y_1744_);
lean_ctor_set(v___x_1769_, 4, v___x_1768_);
lean_ctor_set_uint8(v___x_1769_, sizeof(void*)*5, v___y_1745_);
lean_ctor_set_uint8(v___x_1769_, sizeof(void*)*5 + 1, v___y_1743_);
lean_ctor_set_uint8(v___x_1769_, sizeof(void*)*5 + 2, v_isSilent_1735_);
v___x_1770_ = l_Lean_MessageLog_add(v___x_1769_, v_messages_1761_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 6, v___x_1770_);
v___x_1772_ = v___x_1765_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_env_1755_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v_nextMacroScope_1756_);
lean_ctor_set(v_reuseFailAlloc_1776_, 2, v_ngen_1757_);
lean_ctor_set(v_reuseFailAlloc_1776_, 3, v_auxDeclNGen_1758_);
lean_ctor_set(v_reuseFailAlloc_1776_, 4, v_traceState_1759_);
lean_ctor_set(v_reuseFailAlloc_1776_, 5, v_cache_1760_);
lean_ctor_set(v_reuseFailAlloc_1776_, 6, v___x_1770_);
lean_ctor_set(v_reuseFailAlloc_1776_, 7, v_infoState_1762_);
lean_ctor_set(v_reuseFailAlloc_1776_, 8, v_snapshotTasks_1763_);
v___x_1772_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = lean_st_ref_put(v___y_1750_, v___x_1772_);
v___x_1774_ = lean_box(0);
v___x_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
return v___x_1775_;
}
}
}
v___jp_1778_:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1802_; 
v___x_1787_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1733_);
v___x_1788_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v___x_1787_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1791_ = v___x_1788_;
v_isShared_1792_ = v_isSharedCheck_1802_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1788_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1802_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_inc_ref_n(v___y_1782_, 2);
v___x_1793_ = l_Lean_FileMap_toPosition(v___y_1782_, v___y_1783_);
lean_dec(v___y_1783_);
v___x_1794_ = l_Lean_FileMap_toPosition(v___y_1782_, v___y_1786_);
lean_dec(v___y_1786_);
v___x_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
v___x_1796_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___closed__0));
if (v___y_1781_ == 0)
{
lean_del_object(v___x_1791_);
lean_dec_ref(v___y_1779_);
v___y_1742_ = v___x_1795_;
v___y_1743_ = v___y_1780_;
v___y_1744_ = v___x_1796_;
v___y_1745_ = v___y_1784_;
v___y_1746_ = v___x_1793_;
v___y_1747_ = v___y_1785_;
v___y_1748_ = v_a_1789_;
v___y_1749_ = v___y_1738_;
v___y_1750_ = v___y_1739_;
goto v___jp_1741_;
}
else
{
uint8_t v___x_1797_; 
lean_inc(v_a_1789_);
v___x_1797_ = l_Lean_MessageData_hasTag(v___y_1779_, v_a_1789_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; lean_object* v___x_1800_; 
lean_dec_ref_known(v___x_1795_, 1);
lean_dec_ref(v___x_1793_);
lean_dec(v_a_1789_);
v___x_1798_ = lean_box(0);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 0, v___x_1798_);
v___x_1800_ = v___x_1791_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1798_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
else
{
lean_del_object(v___x_1791_);
v___y_1742_ = v___x_1795_;
v___y_1743_ = v___y_1780_;
v___y_1744_ = v___x_1796_;
v___y_1745_ = v___y_1784_;
v___y_1746_ = v___x_1793_;
v___y_1747_ = v___y_1785_;
v___y_1748_ = v_a_1789_;
v___y_1749_ = v___y_1738_;
v___y_1750_ = v___y_1739_;
goto v___jp_1741_;
}
}
}
}
v___jp_1803_:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Lean_Syntax_getTailPos_x3f(v___y_1809_, v___y_1808_);
lean_dec(v___y_1809_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_inc(v___y_1811_);
v___y_1779_ = v___y_1804_;
v___y_1780_ = v___y_1805_;
v___y_1781_ = v___y_1806_;
v___y_1782_ = v___y_1807_;
v___y_1783_ = v___y_1811_;
v___y_1784_ = v___y_1808_;
v___y_1785_ = v___y_1810_;
v___y_1786_ = v___y_1811_;
goto v___jp_1778_;
}
else
{
lean_object* v_val_1813_; 
v_val_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_val_1813_);
lean_dec_ref_known(v___x_1812_, 1);
v___y_1779_ = v___y_1804_;
v___y_1780_ = v___y_1805_;
v___y_1781_ = v___y_1806_;
v___y_1782_ = v___y_1807_;
v___y_1783_ = v___y_1811_;
v___y_1784_ = v___y_1808_;
v___y_1785_ = v___y_1810_;
v___y_1786_ = v_val_1813_;
goto v___jp_1778_;
}
}
v___jp_1814_:
{
lean_object* v_ref_1822_; lean_object* v___x_1823_; 
v_ref_1822_ = l_Lean_replaceRef(v_ref_1732_, v___y_1820_);
v___x_1823_ = l_Lean_Syntax_getPos_x3f(v_ref_1822_, v___y_1818_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v___x_1824_; 
v___x_1824_ = lean_unsigned_to_nat(0u);
v___y_1804_ = v___y_1815_;
v___y_1805_ = v___y_1821_;
v___y_1806_ = v___y_1816_;
v___y_1807_ = v___y_1817_;
v___y_1808_ = v___y_1818_;
v___y_1809_ = v_ref_1822_;
v___y_1810_ = v___y_1819_;
v___y_1811_ = v___x_1824_;
goto v___jp_1803_;
}
else
{
lean_object* v_val_1825_; 
v_val_1825_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_val_1825_);
lean_dec_ref_known(v___x_1823_, 1);
v___y_1804_ = v___y_1815_;
v___y_1805_ = v___y_1821_;
v___y_1806_ = v___y_1816_;
v___y_1807_ = v___y_1817_;
v___y_1808_ = v___y_1818_;
v___y_1809_ = v_ref_1822_;
v___y_1810_ = v___y_1819_;
v___y_1811_ = v_val_1825_;
goto v___jp_1803_;
}
}
v___jp_1827_:
{
if (v___y_1834_ == 0)
{
v___y_1815_ = v___y_1830_;
v___y_1816_ = v___y_1831_;
v___y_1817_ = v___y_1828_;
v___y_1818_ = v___y_1832_;
v___y_1819_ = v___y_1829_;
v___y_1820_ = v___y_1833_;
v___y_1821_ = v_severity_1734_;
goto v___jp_1814_;
}
else
{
v___y_1815_ = v___y_1830_;
v___y_1816_ = v___y_1831_;
v___y_1817_ = v___y_1828_;
v___y_1818_ = v___y_1832_;
v___y_1819_ = v___y_1829_;
v___y_1820_ = v___y_1833_;
v___y_1821_ = v___x_1826_;
goto v___jp_1814_;
}
}
v___jp_1835_:
{
if (v___y_1836_ == 0)
{
lean_object* v_toCold_1837_; lean_object* v_ref_1838_; uint8_t v_suppressElabErrors_1839_; lean_object* v_fileName_1840_; lean_object* v_fileMap_1841_; lean_object* v_options_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___f_1845_; uint8_t v___x_1846_; uint8_t v___x_1847_; 
v_toCold_1837_ = lean_ctor_get(v___y_1738_, 0);
v_ref_1838_ = lean_ctor_get(v___y_1738_, 2);
v_suppressElabErrors_1839_ = lean_ctor_get_uint8(v___y_1738_, sizeof(void*)*3 + 1);
v_fileName_1840_ = lean_ctor_get(v_toCold_1837_, 0);
v_fileMap_1841_ = lean_ctor_get(v_toCold_1837_, 1);
v_options_1842_ = lean_ctor_get(v_toCold_1837_, 2);
v___x_1843_ = lean_box(v_suppressElabErrors_1839_);
v___x_1844_ = lean_box(v___y_1836_);
v___f_1845_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1845_, 0, v___x_1843_);
lean_closure_set(v___f_1845_, 1, v___x_1844_);
v___x_1846_ = 1;
v___x_1847_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1734_, v___x_1846_);
if (v___x_1847_ == 0)
{
v___y_1828_ = v_fileMap_1841_;
v___y_1829_ = v_fileName_1840_;
v___y_1830_ = v___f_1845_;
v___y_1831_ = v_suppressElabErrors_1839_;
v___y_1832_ = v___y_1836_;
v___y_1833_ = v_ref_1838_;
v___y_1834_ = v___x_1847_;
goto v___jp_1827_;
}
else
{
lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1848_ = l_Lean_warningAsError;
v___x_1849_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_1842_, v___x_1848_);
v___y_1828_ = v_fileMap_1841_;
v___y_1829_ = v_fileName_1840_;
v___y_1830_ = v___f_1845_;
v___y_1831_ = v_suppressElabErrors_1839_;
v___y_1832_ = v___y_1836_;
v___y_1833_ = v_ref_1838_;
v___y_1834_ = v___x_1849_;
goto v___jp_1827_;
}
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_dec_ref(v_msgData_1733_);
v___x_1850_ = lean_box(0);
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
return v___x_1851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_1854_, lean_object* v_msgData_1855_, lean_object* v_severity_1856_, lean_object* v_isSilent_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
uint8_t v_severity_boxed_1863_; uint8_t v_isSilent_boxed_1864_; lean_object* v_res_1865_; 
v_severity_boxed_1863_ = lean_unbox(v_severity_1856_);
v_isSilent_boxed_1864_ = lean_unbox(v_isSilent_1857_);
v_res_1865_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(v_ref_1854_, v_msgData_1855_, v_severity_boxed_1863_, v_isSilent_boxed_1864_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v_ref_1854_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(lean_object* v_msgData_1866_, uint8_t v_severity_1867_, uint8_t v_isSilent_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v_ref_1874_; lean_object* v___x_1875_; 
v_ref_1874_ = lean_ctor_get(v___y_1871_, 2);
v___x_1875_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(v_ref_1874_, v_msgData_1866_, v_severity_1867_, v_isSilent_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0___boxed(lean_object* v_msgData_1876_, lean_object* v_severity_1877_, lean_object* v_isSilent_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
uint8_t v_severity_boxed_1884_; uint8_t v_isSilent_boxed_1885_; lean_object* v_res_1886_; 
v_severity_boxed_1884_ = lean_unbox(v_severity_1877_);
v_isSilent_boxed_1885_ = lean_unbox(v_isSilent_1878_);
v_res_1886_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(v_msgData_1876_, v_severity_boxed_1884_, v_isSilent_boxed_1885_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(lean_object* v_msgData_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
uint8_t v___x_1893_; uint8_t v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = 1;
v___x_1894_ = 0;
v___x_1895_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(v_msgData_1887_, v___x_1893_, v___x_1894_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0___boxed(lean_object* v_msgData_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(v_msgData_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
return v_res_1902_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__0));
v___x_1905_ = l_Lean_stringToMessageData(v___x_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0(uint8_t v___x_1906_, lean_object* v___x_1907_, lean_object* v___x_1908_, lean_object* v___x_1909_, lean_object* v___x_1910_, lean_object* v_tk_1911_, lean_object* v_typesStx_1912_, lean_object* v___x_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_ref_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___y_1929_; 
v_ref_1919_ = lean_ctor_get(v___y_1916_, 2);
v___x_1920_ = l_Lean_SourceInfo_fromRef(v_ref_1919_, v___x_1906_);
v___x_1921_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__1));
v___x_1922_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__2));
v___x_1923_ = l_Lean_Name_mkStr4(v___x_1907_, v___x_1908_, v___x_1909_, v___x_1922_);
v___x_1924_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3));
lean_inc(v___x_1920_);
v___x_1925_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1920_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5));
v___x_1927_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6);
if (lean_obj_tag(v_typesStx_1912_) == 1)
{
lean_object* v_val_1950_; lean_object* v___x_1951_; 
v_val_1950_ = lean_ctor_get(v_typesStx_1912_, 0);
lean_inc(v_val_1950_);
lean_dec_ref_known(v_typesStx_1912_, 1);
v___x_1951_ = l_Array_mkArray1___redArg(v_val_1950_);
v___y_1929_ = v___x_1951_;
goto v___jp_1928_;
}
else
{
lean_object* v___x_1952_; 
lean_dec(v_typesStx_1912_);
v___x_1952_ = lean_mk_empty_array_with_capacity(v___x_1913_);
v___y_1929_ = v___x_1952_;
goto v___jp_1928_;
}
v___jp_1928_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1, &l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1);
v___x_1931_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(v___x_1930_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1948_; 
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1948_ == 0)
{
lean_object* v_unused_1949_; 
v_unused_1949_ = lean_ctor_get(v___x_1931_, 0);
lean_dec(v_unused_1949_);
v___x_1933_ = v___x_1931_;
v_isShared_1934_ = v_isSharedCheck_1948_;
goto v_resetjp_1932_;
}
else
{
lean_dec(v___x_1931_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1948_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1935_ = l_Array_append___redArg(v___x_1927_, v___y_1929_);
lean_dec_ref(v___y_1929_);
lean_inc(v___x_1920_);
v___x_1936_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1920_);
lean_ctor_set(v___x_1936_, 1, v___x_1926_);
lean_ctor_set(v___x_1936_, 2, v___x_1935_);
v___x_1937_ = l_Lean_Syntax_node3(v___x_1920_, v___x_1923_, v___x_1925_, v___x_1910_, v___x_1936_);
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1921_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = lean_box(0);
v___x_1940_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1938_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
lean_ctor_set(v___x_1940_, 2, v___x_1939_);
lean_ctor_set(v___x_1940_, 3, v___x_1939_);
lean_ctor_set(v___x_1940_, 4, v___x_1939_);
lean_ctor_set(v___x_1940_, 5, v___x_1939_);
lean_inc(v_ref_1919_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set_tag(v___x_1933_, 1);
lean_ctor_set(v___x_1933_, 0, v_ref_1919_);
v___x_1942_ = v___x_1933_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_ref_1919_);
v___x_1942_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
lean_object* v___x_1943_; uint8_t v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1943_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__7));
v___x_1944_ = 4;
v___x_1945_ = l_Lean_MessageData_nil;
v___x_1946_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1911_, v___x_1940_, v___x_1942_, v___x_1943_, v___x_1939_, v___x_1944_, v___x_1945_, v___y_1916_, v___y_1917_);
return v___x_1946_;
}
}
}
else
{
lean_dec_ref(v___y_1929_);
lean_dec_ref_known(v___x_1925_, 2);
lean_dec(v___x_1923_);
lean_dec(v___x_1920_);
lean_dec(v_tk_1911_);
lean_dec(v___x_1910_);
return v___x_1931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___boxed(lean_object* v___x_1953_, lean_object* v___x_1954_, lean_object* v___x_1955_, lean_object* v___x_1956_, lean_object* v___x_1957_, lean_object* v_tk_1958_, lean_object* v_typesStx_1959_, lean_object* v___x_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
uint8_t v___x_7755__boxed_1966_; lean_object* v_res_1967_; 
v___x_7755__boxed_1966_ = lean_unbox(v___x_1953_);
v_res_1967_ = l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0(v___x_7755__boxed_1966_, v___x_1954_, v___x_1955_, v___x_1956_, v___x_1957_, v_tk_1958_, v_typesStx_1959_, v___x_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___x_1960_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic(lean_object* v_x_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; 
v___x_1986_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0));
v___x_1987_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1));
v___x_1988_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1));
v___x_1989_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0));
lean_inc(v_x_1976_);
v___x_1990_ = l_Lean_Syntax_isOfKind(v_x_1976_, v___x_1989_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1991_; 
lean_dec(v_x_1976_);
v___x_1991_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1991_;
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v___x_1992_ = lean_unsigned_to_nat(1u);
v___x_1993_ = l_Lean_Syntax_getArg(v_x_1976_, v___x_1992_);
v___x_1994_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_1993_);
v___x_1995_ = l_Lean_Syntax_isOfKind(v___x_1993_, v___x_1994_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; 
lean_dec(v___x_1993_);
lean_dec(v_x_1976_);
v___x_1996_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1996_;
}
else
{
lean_object* v___x_1997_; lean_object* v_tk_1998_; lean_object* v_typesStx_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___x_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; 
v___x_1997_ = lean_unsigned_to_nat(0u);
v_tk_1998_ = l_Lean_Syntax_getArg(v_x_1976_, v___x_1997_);
v___x_2093_ = lean_unsigned_to_nat(2u);
v___x_2094_ = l_Lean_Syntax_getArg(v_x_1976_, v___x_2093_);
v___x_2095_ = l_Lean_Syntax_isNone(v___x_2094_);
if (v___x_2095_ == 0)
{
uint8_t v___x_2096_; 
lean_inc(v___x_2094_);
v___x_2096_ = l_Lean_Syntax_matchesNull(v___x_2094_, v___x_1992_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; 
lean_dec(v___x_2094_);
lean_dec(v_tk_1998_);
lean_dec(v___x_1993_);
lean_dec(v_x_1976_);
v___x_2097_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2097_;
}
else
{
lean_object* v_typesStx_2098_; 
v_typesStx_2098_ = l_Lean_Syntax_getArg(v___x_2094_, v___x_1997_);
lean_dec(v___x_2094_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2101_; uint8_t v___x_2102_; 
v___x_2101_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_typesStx_2098_);
v___x_2102_ = l_Lean_Syntax_isOfKind(v_typesStx_2098_, v___x_2101_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; 
lean_dec(v_typesStx_2098_);
lean_dec(v_tk_1998_);
lean_dec(v___x_1993_);
lean_dec(v_x_1976_);
v___x_2103_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2103_;
}
else
{
goto v___jp_2099_;
}
}
else
{
goto v___jp_2099_;
}
v___jp_2099_:
{
lean_object* v___x_2100_; 
v___x_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2100_, 0, v_typesStx_2098_);
v_typesStx_2000_ = v___x_2100_;
v___y_2001_ = v_a_1977_;
v___y_2002_ = v_a_1978_;
v___y_2003_ = v_a_1979_;
v___y_2004_ = v_a_1980_;
v___y_2005_ = v_a_1981_;
v___y_2006_ = v_a_1982_;
v___y_2007_ = v_a_1983_;
v___y_2008_ = v_a_1984_;
goto v___jp_1999_;
}
}
}
else
{
lean_object* v___x_2104_; 
lean_dec(v___x_2094_);
v___x_2104_ = lean_box(0);
v_typesStx_2000_ = v___x_2104_;
v___y_2001_ = v_a_1977_;
v___y_2002_ = v_a_1978_;
v___y_2003_ = v_a_1979_;
v___y_2004_ = v_a_1980_;
v___y_2005_ = v_a_1981_;
v___y_2006_ = v_a_1982_;
v___y_2007_ = v_a_1983_;
v___y_2008_ = v_a_1984_;
goto v___jp_1999_;
}
v___jp_1999_:
{
lean_object* v___x_2009_; lean_object* v_path_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; 
v___x_2009_ = lean_unsigned_to_nat(3u);
v_path_2010_ = l_Lean_Syntax_getArg(v_x_1976_, v___x_2009_);
lean_dec(v_x_1976_);
v___x_2011_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__2));
lean_inc(v_path_2010_);
v___x_2012_ = l_Lean_Syntax_isOfKind(v_path_2010_, v___x_2011_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; 
lean_dec(v_path_2010_);
lean_dec(v_typesStx_2000_);
lean_dec(v_tk_1998_);
lean_dec(v___x_1993_);
v___x_2013_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2013_;
}
else
{
lean_object* v___x_2014_; 
v___x_2014_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_2007_, v___y_2008_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2091_; 
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2091_ == 0)
{
lean_object* v_unused_2092_; 
v_unused_2092_ = lean_ctor_get(v___x_2014_, 0);
lean_dec(v_unused_2092_);
v___x_2016_ = v___x_2014_;
v_isShared_2017_ = v_isSharedCheck_2091_;
goto v_resetjp_2015_;
}
else
{
lean_dec(v___x_2014_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2091_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2018_; uint8_t v___x_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2018_ = lean_unsigned_to_nat(10u);
v___x_2019_ = 0;
v___x_2020_ = lean_unsigned_to_nat(100000u);
v___x_2021_ = 0;
v___x_2022_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_2022_, 0, v___x_2018_);
lean_ctor_set(v___x_2022_, 1, v___x_2020_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*2, v___x_1995_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*2 + 1, v___x_1995_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*2 + 2, v___x_2019_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*2 + 3, v___x_1995_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*2 + 4, v___x_1995_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*2 + 5, v___x_1995_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*2 + 6, v___x_1995_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*2 + 7, v___x_1995_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*2 + 8, v___x_2019_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*2 + 9, v___x_2019_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*2 + 10, v___x_2021_);
lean_inc(v___x_1993_);
v___x_2023_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_1993_, v___x_2022_, v___x_1995_, v___y_2001_, v___y_2007_, v___y_2008_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2025_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
lean_inc(v_typesStx_2000_);
v___x_2025_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_2000_, v_a_2024_, v___y_2007_, v___y_2008_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_2025_, 1);
v___x_2027_ = l_Lean_TSyntax_getString(v_path_2010_);
lean_dec(v_path_2010_);
v___x_2028_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v___x_2027_, v_a_2024_, v_a_2026_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v___x_2030_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc(v_a_2029_);
lean_dec_ref_known(v___x_2028_, 1);
v___x_2030_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2002_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2031_);
lean_dec_ref_known(v___x_2030_, 1);
v___x_2032_ = lean_unsigned_to_nat(9u);
v___x_2033_ = lean_unsigned_to_nat(5u);
v___x_2034_ = lean_unsigned_to_nat(8u);
v___x_2035_ = lean_unsigned_to_nat(1000u);
v___x_2036_ = lean_unsigned_to_nat(1024u);
v___x_2037_ = lean_unsigned_to_nat(10000u);
v___x_2038_ = lean_unsigned_to_nat(1048576u);
v___x_2039_ = lean_unsigned_to_nat(50u);
v___x_2040_ = lean_box(0);
v___x_2041_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_2041_, 0, v___x_2032_);
lean_ctor_set(v___x_2041_, 1, v___x_2033_);
lean_ctor_set(v___x_2041_, 2, v___x_2034_);
lean_ctor_set(v___x_2041_, 3, v___x_2034_);
lean_ctor_set(v___x_2041_, 4, v___x_2035_);
lean_ctor_set(v___x_2041_, 5, v___x_2035_);
lean_ctor_set(v___x_2041_, 6, v___x_2020_);
lean_ctor_set(v___x_2041_, 7, v___x_2036_);
lean_ctor_set(v___x_2041_, 8, v___x_2037_);
lean_ctor_set(v___x_2041_, 9, v___x_2035_);
lean_ctor_set(v___x_2041_, 10, v___x_2038_);
lean_ctor_set(v___x_2041_, 11, v___x_2018_);
lean_ctor_set(v___x_2041_, 12, v___x_2039_);
lean_ctor_set(v___x_2041_, 13, v___x_2040_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14, v___x_2019_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 1, v___x_2019_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 2, v___x_2019_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 3, v___x_2019_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 4, v___x_2019_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 5, v___x_1995_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 6, v___x_1995_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 7, v___x_1995_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 8, v___x_2019_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 9, v___x_2019_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 10, v___x_1995_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 11, v___x_2019_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 12, v___x_1995_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 13, v___x_1995_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 14, v___x_1995_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 15, v___x_1995_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 16, v___x_1995_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 17, v___x_2019_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 18, v___x_1995_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 19, v___x_1995_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 20, v___x_1995_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 21, v___x_1995_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 22, v___x_1995_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 23, v___x_1995_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 24, v___x_1995_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 25, v___x_1995_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 26, v___x_1995_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 27, v___x_1995_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 28, v___x_1995_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 29, v___x_1995_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 30, v___x_2019_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 31, v___x_1995_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*14 + 32, v___x_1995_);
v___x_2042_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_2041_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2044_; lean_object* v___f_2045_; lean_object* v___x_2047_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2043_);
lean_dec_ref_known(v___x_2042_, 1);
v___x_2044_ = lean_box(v___x_2019_);
v___f_2045_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___boxed), 13, 8);
lean_closure_set(v___f_2045_, 0, v___x_2044_);
lean_closure_set(v___f_2045_, 1, v___x_1986_);
lean_closure_set(v___f_2045_, 2, v___x_1987_);
lean_closure_set(v___f_2045_, 3, v___x_1988_);
lean_closure_set(v___f_2045_, 4, v___x_1993_);
lean_closure_set(v___f_2045_, 5, v_tk_1998_);
lean_closure_set(v___f_2045_, 6, v_typesStx_2000_);
lean_closure_set(v___f_2045_, 7, v___x_1997_);
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v_a_2031_);
v___x_2047_ = v___x_2016_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2031_);
v___x_2047_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed), 13, 3);
lean_closure_set(v___x_2048_, 0, v___x_2047_);
lean_closure_set(v___x_2048_, 1, v_a_2029_);
lean_closure_set(v___x_2048_, 2, v___f_2045_);
v___x_2049_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___x_2048_, v_a_2043_, v___x_2040_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
return v___x_2049_;
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec(v_a_2031_);
lean_dec(v_a_2029_);
lean_del_object(v___x_2016_);
lean_dec(v_typesStx_2000_);
lean_dec(v_tk_1998_);
lean_dec(v___x_1993_);
v_a_2051_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2042_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2042_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec(v_a_2029_);
lean_del_object(v___x_2016_);
lean_dec(v_typesStx_2000_);
lean_dec(v_tk_1998_);
lean_dec(v___x_1993_);
v_a_2059_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2030_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2030_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_del_object(v___x_2016_);
lean_dec(v_typesStx_2000_);
lean_dec(v_tk_1998_);
lean_dec(v___x_1993_);
v_a_2067_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2028_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2028_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec(v_a_2024_);
lean_del_object(v___x_2016_);
lean_dec(v_path_2010_);
lean_dec(v_typesStx_2000_);
lean_dec(v_tk_1998_);
lean_dec(v___x_1993_);
v_a_2075_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2025_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2025_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_del_object(v___x_2016_);
lean_dec(v_path_2010_);
lean_dec(v_typesStx_2000_);
lean_dec(v_tk_1998_);
lean_dec(v___x_1993_);
v_a_2083_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2023_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2023_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
}
else
{
lean_dec(v_path_2010_);
lean_dec(v_typesStx_2000_);
lean_dec(v_tk_1998_);
lean_dec(v___x_1993_);
return v___x_2014_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___boxed(lean_object* v_x_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic(v_x_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
lean_dec(v_a_2113_);
lean_dec_ref(v_a_2112_);
lean_dec(v_a_2111_);
lean_dec_ref(v_a_2110_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
lean_dec(v_a_2107_);
lean_dec_ref(v_a_2106_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1(){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2124_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2125_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0));
v___x_2126_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___closed__1));
v___x_2127_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___boxed), 10, 0);
v___x_2128_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2124_, v___x_2125_, v___x_2126_, v___x_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___boxed(lean_object* v_a_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1();
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0(lean_object* v___x_2131_, uint8_t v___x_2132_, lean_object* v___x_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2144_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2);
v___x_2145_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5);
v___x_2146_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6));
v___x_2147_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2147_, 0, v___x_2144_);
lean_ctor_set(v___x_2147_, 1, v___x_2145_);
lean_ctor_set(v___x_2147_, 2, v___x_2131_);
lean_ctor_set(v___x_2147_, 3, v___x_2146_);
lean_ctor_set_uint8(v___x_2147_, sizeof(void*)*4, v___x_2132_);
v___x_2148_ = lean_st_mk_ref(v___x_2147_);
v___x_2149_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_2133_, v___x_2148_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2159_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2152_ = v___x_2149_;
v_isShared_2153_ = v_isSharedCheck_2159_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2149_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2159_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2157_; 
v___x_2154_ = lean_st_ref_get(v___x_2148_);
lean_dec(v___x_2148_);
v___x_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2155_, 0, v_a_2150_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2155_);
v___x_2157_ = v___x_2152_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2155_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_dec(v___x_2148_);
v_a_2160_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2149_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2149_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0___boxed(lean_object* v___x_2168_, lean_object* v___x_2169_, lean_object* v___x_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
uint8_t v___x_3442__boxed_2181_; lean_object* v_res_2182_; 
v___x_3442__boxed_2181_ = lean_unbox(v___x_2169_);
v_res_2182_ = l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0(v___x_2168_, v___x_3442__boxed_2181_, v___x_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v___x_2170_);
return v_res_2182_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_2183_, lean_object* v_i_2184_, lean_object* v_k_2185_){
_start:
{
lean_object* v___x_2186_; uint8_t v___x_2187_; 
v___x_2186_ = lean_array_get_size(v_keys_2183_);
v___x_2187_ = lean_nat_dec_lt(v_i_2184_, v___x_2186_);
if (v___x_2187_ == 0)
{
lean_dec(v_i_2184_);
return v___x_2187_;
}
else
{
lean_object* v_k_x27_2188_; uint8_t v___x_2189_; 
v_k_x27_2188_ = lean_array_fget_borrowed(v_keys_2183_, v_i_2184_);
v___x_2189_ = l_Lean_instBEqMVarId_beq(v_k_2185_, v_k_x27_2188_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = lean_unsigned_to_nat(1u);
v___x_2191_ = lean_nat_add(v_i_2184_, v___x_2190_);
lean_dec(v_i_2184_);
v_i_2184_ = v___x_2191_;
goto _start;
}
else
{
lean_dec(v_i_2184_);
return v___x_2187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_2193_, lean_object* v_i_2194_, lean_object* v_k_2195_){
_start:
{
uint8_t v_res_2196_; lean_object* v_r_2197_; 
v_res_2196_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2193_, v_i_2194_, v_k_2195_);
lean_dec(v_k_2195_);
lean_dec_ref(v_keys_2193_);
v_r_2197_ = lean_box(v_res_2196_);
return v_r_2197_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2198_, size_t v_x_2199_, lean_object* v_x_2200_){
_start:
{
if (lean_obj_tag(v_x_2198_) == 0)
{
lean_object* v_es_2201_; lean_object* v___x_2202_; size_t v___x_2203_; size_t v___x_2204_; lean_object* v_j_2205_; lean_object* v___x_2206_; 
v_es_2201_ = lean_ctor_get(v_x_2198_, 0);
v___x_2202_ = lean_box(2);
v___x_2203_ = ((size_t)31ULL);
v___x_2204_ = lean_usize_land(v_x_2199_, v___x_2203_);
v_j_2205_ = lean_usize_to_nat(v___x_2204_);
v___x_2206_ = lean_array_get_borrowed(v___x_2202_, v_es_2201_, v_j_2205_);
lean_dec(v_j_2205_);
switch(lean_obj_tag(v___x_2206_))
{
case 0:
{
lean_object* v_key_2207_; uint8_t v___x_2208_; 
v_key_2207_ = lean_ctor_get(v___x_2206_, 0);
v___x_2208_ = l_Lean_instBEqMVarId_beq(v_x_2200_, v_key_2207_);
return v___x_2208_;
}
case 1:
{
lean_object* v_node_2209_; size_t v___x_2210_; size_t v___x_2211_; 
v_node_2209_ = lean_ctor_get(v___x_2206_, 0);
v___x_2210_ = ((size_t)5ULL);
v___x_2211_ = lean_usize_shift_right(v_x_2199_, v___x_2210_);
v_x_2198_ = v_node_2209_;
v_x_2199_ = v___x_2211_;
goto _start;
}
default: 
{
uint8_t v___x_2213_; 
v___x_2213_ = 0;
return v___x_2213_;
}
}
}
else
{
lean_object* v_ks_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; 
v_ks_2214_ = lean_ctor_get(v_x_2198_, 0);
v___x_2215_ = lean_unsigned_to_nat(0u);
v___x_2216_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_2214_, v___x_2215_, v_x_2200_);
return v___x_2216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2217_, lean_object* v_x_2218_, lean_object* v_x_2219_){
_start:
{
size_t v_x_3548__boxed_2220_; uint8_t v_res_2221_; lean_object* v_r_2222_; 
v_x_3548__boxed_2220_ = lean_unbox_usize(v_x_2218_);
lean_dec(v_x_2218_);
v_res_2221_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_2217_, v_x_3548__boxed_2220_, v_x_2219_);
lean_dec(v_x_2219_);
lean_dec_ref(v_x_2217_);
v_r_2222_ = lean_box(v_res_2221_);
return v_r_2222_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(lean_object* v_x_2223_, lean_object* v_x_2224_){
_start:
{
uint64_t v___x_2225_; size_t v___x_2226_; uint8_t v___x_2227_; 
v___x_2225_ = l_Lean_instHashableMVarId_hash(v_x_2224_);
v___x_2226_ = lean_uint64_to_usize(v___x_2225_);
v___x_2227_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_2223_, v___x_2226_, v_x_2224_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_2228_, lean_object* v_x_2229_){
_start:
{
uint8_t v_res_2230_; lean_object* v_r_2231_; 
v_res_2230_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(v_x_2228_, v_x_2229_);
lean_dec(v_x_2229_);
lean_dec_ref(v_x_2228_);
v_r_2231_ = lean_box(v_res_2230_);
return v_r_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(lean_object* v_mvarId_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v___x_2235_; lean_object* v_mctx_2236_; lean_object* v_eAssignment_2237_; uint8_t v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2235_ = lean_st_ref_get(v___y_2233_);
v_mctx_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc_ref(v_mctx_2236_);
lean_dec(v___x_2235_);
v_eAssignment_2237_ = lean_ctor_get(v_mctx_2236_, 8);
lean_inc_ref(v_eAssignment_2237_);
lean_dec_ref(v_mctx_2236_);
v___x_2238_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(v_eAssignment_2237_, v_mvarId_2232_);
lean_dec_ref(v_eAssignment_2237_);
v___x_2239_ = lean_box(v___x_2238_);
v___x_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg___boxed(lean_object* v_mvarId_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(v_mvarId_2241_, v___y_2242_);
lean_dec(v___y_2242_);
lean_dec(v_mvarId_2241_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1(size_t v_sz_2245_, size_t v_i_2246_, lean_object* v_bs_2247_){
_start:
{
uint8_t v___x_2248_; 
v___x_2248_ = lean_usize_dec_lt(v_i_2246_, v_sz_2245_);
if (v___x_2248_ == 0)
{
return v_bs_2247_;
}
else
{
lean_object* v_v_2249_; lean_object* v_name_2250_; lean_object* v_type_2251_; lean_object* v_value_2252_; lean_object* v___x_2253_; lean_object* v_bs_x27_2254_; uint8_t v___x_2255_; uint8_t v___x_2256_; lean_object* v___x_2257_; size_t v___x_2258_; size_t v___x_2259_; lean_object* v___x_2260_; 
v_v_2249_ = lean_array_uget_borrowed(v_bs_2247_, v_i_2246_);
v_name_2250_ = lean_ctor_get(v_v_2249_, 0);
lean_inc(v_name_2250_);
v_type_2251_ = lean_ctor_get(v_v_2249_, 1);
lean_inc_ref(v_type_2251_);
v_value_2252_ = lean_ctor_get(v_v_2249_, 2);
lean_inc_ref(v_value_2252_);
v___x_2253_ = lean_unsigned_to_nat(0u);
v_bs_x27_2254_ = lean_array_uset(v_bs_2247_, v_i_2246_, v___x_2253_);
v___x_2255_ = 0;
v___x_2256_ = 0;
v___x_2257_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2257_, 0, v_name_2250_);
lean_ctor_set(v___x_2257_, 1, v_type_2251_);
lean_ctor_set(v___x_2257_, 2, v_value_2252_);
lean_ctor_set_uint8(v___x_2257_, sizeof(void*)*3, v___x_2255_);
lean_ctor_set_uint8(v___x_2257_, sizeof(void*)*3 + 1, v___x_2256_);
v___x_2258_ = ((size_t)1ULL);
v___x_2259_ = lean_usize_add(v_i_2246_, v___x_2258_);
v___x_2260_ = lean_array_uset(v_bs_x27_2254_, v_i_2246_, v___x_2257_);
v_i_2246_ = v___x_2259_;
v_bs_2247_ = v___x_2260_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1___boxed(lean_object* v_sz_2262_, lean_object* v_i_2263_, lean_object* v_bs_2264_){
_start:
{
size_t v_sz_boxed_2265_; size_t v_i_boxed_2266_; lean_object* v_res_2267_; 
v_sz_boxed_2265_ = lean_unbox_usize(v_sz_2262_);
lean_dec(v_sz_2262_);
v_i_boxed_2266_ = lean_unbox_usize(v_i_2263_);
lean_dec(v_i_2263_);
v_res_2267_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1(v_sz_boxed_2265_, v_i_boxed_2266_, v_bs_2264_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize(lean_object* v_x_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_){
_start:
{
lean_object* v___x_2283_; uint8_t v___x_2284_; 
v___x_2283_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0));
lean_inc(v_x_2273_);
v___x_2284_ = l_Lean_Syntax_isOfKind(v_x_2273_, v___x_2283_);
if (v___x_2284_ == 0)
{
lean_object* v___x_2285_; 
lean_dec(v_x_2273_);
v___x_2285_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2285_;
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; lean_object* v_types_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; 
v___x_2286_ = lean_unsigned_to_nat(1u);
v___x_2287_ = l_Lean_Syntax_getArg(v_x_2273_, v___x_2286_);
v___x_2288_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_2287_);
v___x_2289_ = l_Lean_Syntax_isOfKind(v___x_2287_, v___x_2288_);
if (v___x_2289_ == 0)
{
lean_object* v___x_2411_; 
lean_dec(v___x_2287_);
lean_dec(v_x_2273_);
v___x_2411_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2411_;
}
else
{
lean_object* v___x_2412_; lean_object* v___x_2413_; uint8_t v___x_2414_; 
v___x_2412_ = lean_unsigned_to_nat(2u);
v___x_2413_ = l_Lean_Syntax_getArg(v_x_2273_, v___x_2412_);
lean_dec(v_x_2273_);
v___x_2414_ = l_Lean_Syntax_isNone(v___x_2413_);
if (v___x_2414_ == 0)
{
uint8_t v___x_2415_; 
lean_inc(v___x_2413_);
v___x_2415_ = l_Lean_Syntax_matchesNull(v___x_2413_, v___x_2286_);
if (v___x_2415_ == 0)
{
lean_object* v___x_2416_; 
lean_dec(v___x_2413_);
lean_dec(v___x_2287_);
v___x_2416_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2416_;
}
else
{
lean_object* v___x_2417_; lean_object* v_types_2418_; 
v___x_2417_ = lean_unsigned_to_nat(0u);
v_types_2418_ = l_Lean_Syntax_getArg(v___x_2413_, v___x_2417_);
lean_dec(v___x_2413_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2421_; uint8_t v___x_2422_; 
v___x_2421_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_types_2418_);
v___x_2422_ = l_Lean_Syntax_isOfKind(v_types_2418_, v___x_2421_);
if (v___x_2422_ == 0)
{
lean_object* v___x_2423_; 
lean_dec(v_types_2418_);
lean_dec(v___x_2287_);
v___x_2423_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2423_;
}
else
{
goto v___jp_2419_;
}
}
else
{
goto v___jp_2419_;
}
v___jp_2419_:
{
lean_object* v___x_2420_; 
v___x_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2420_, 0, v_types_2418_);
v_types_2291_ = v___x_2420_;
v___y_2292_ = v_a_2274_;
v___y_2293_ = v_a_2275_;
v___y_2294_ = v_a_2276_;
v___y_2295_ = v_a_2277_;
v___y_2296_ = v_a_2278_;
v___y_2297_ = v_a_2279_;
v___y_2298_ = v_a_2280_;
v___y_2299_ = v_a_2281_;
goto v___jp_2290_;
}
}
}
else
{
lean_object* v___x_2424_; 
lean_dec(v___x_2413_);
v___x_2424_ = lean_box(0);
v_types_2291_ = v___x_2424_;
v___y_2292_ = v_a_2274_;
v___y_2293_ = v_a_2275_;
v___y_2294_ = v_a_2276_;
v___y_2295_ = v_a_2277_;
v___y_2296_ = v_a_2278_;
v___y_2297_ = v_a_2279_;
v___y_2298_ = v_a_2280_;
v___y_2299_ = v_a_2281_;
goto v___jp_2290_;
}
}
v___jp_2290_:
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2409_; 
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2409_ == 0)
{
lean_object* v_unused_2410_; 
v_unused_2410_ = lean_ctor_get(v___x_2300_, 0);
lean_dec(v_unused_2410_);
v___x_2302_ = v___x_2300_;
v_isShared_2303_ = v_isSharedCheck_2409_;
goto v_resetjp_2301_;
}
else
{
lean_dec(v___x_2300_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2409_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2304_; uint8_t v___x_2305_; lean_object* v___x_2306_; uint8_t v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2304_ = lean_unsigned_to_nat(10u);
v___x_2305_ = 0;
v___x_2306_ = lean_unsigned_to_nat(100000u);
v___x_2307_ = 0;
v___x_2308_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_2308_, 0, v___x_2304_);
lean_ctor_set(v___x_2308_, 1, v___x_2306_);
lean_ctor_set_uint8(v___x_2308_, sizeof(void*)*2, v___x_2289_);
lean_ctor_set_uint8(v___x_2308_, sizeof(void*)*2 + 1, v___x_2289_);
lean_ctor_set_uint8(v___x_2308_, sizeof(void*)*2 + 2, v___x_2305_);
lean_ctor_set_uint8(v___x_2308_, sizeof(void*)*2 + 3, v___x_2289_);
lean_ctor_set_uint8(v___x_2308_, sizeof(void*)*2 + 4, v___x_2289_);
lean_ctor_set_uint8(v___x_2308_, sizeof(void*)*2 + 5, v___x_2289_);
lean_ctor_set_uint8(v___x_2308_, sizeof(void*)*2 + 6, v___x_2289_);
lean_ctor_set_uint8(v___x_2308_, sizeof(void*)*2 + 7, v___x_2289_);
lean_ctor_set_uint8(v___x_2308_, sizeof(void*)*2 + 8, v___x_2305_);
lean_ctor_set_uint8(v___x_2308_, sizeof(void*)*2 + 9, v___x_2305_);
lean_ctor_set_uint8(v___x_2308_, sizeof(void*)*2 + 10, v___x_2307_);
v___x_2309_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_2287_, v___x_2308_, v___x_2289_, v___y_2292_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2311_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2310_);
lean_dec_ref_known(v___x_2309_, 1);
v___x_2311_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_types_2291_, v_a_2310_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2313_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2311_, 1);
v___x_2313_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2293_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref_known(v___x_2313_, 1);
v___x_2315_ = lean_unsigned_to_nat(9u);
v___x_2316_ = lean_unsigned_to_nat(5u);
v___x_2317_ = lean_unsigned_to_nat(8u);
v___x_2318_ = lean_unsigned_to_nat(1000u);
v___x_2319_ = lean_unsigned_to_nat(1024u);
v___x_2320_ = lean_unsigned_to_nat(10000u);
v___x_2321_ = lean_unsigned_to_nat(1048576u);
v___x_2322_ = lean_unsigned_to_nat(50u);
v___x_2323_ = lean_box(0);
v___x_2324_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_2324_, 0, v___x_2315_);
lean_ctor_set(v___x_2324_, 1, v___x_2316_);
lean_ctor_set(v___x_2324_, 2, v___x_2317_);
lean_ctor_set(v___x_2324_, 3, v___x_2317_);
lean_ctor_set(v___x_2324_, 4, v___x_2318_);
lean_ctor_set(v___x_2324_, 5, v___x_2318_);
lean_ctor_set(v___x_2324_, 6, v___x_2306_);
lean_ctor_set(v___x_2324_, 7, v___x_2319_);
lean_ctor_set(v___x_2324_, 8, v___x_2320_);
lean_ctor_set(v___x_2324_, 9, v___x_2318_);
lean_ctor_set(v___x_2324_, 10, v___x_2321_);
lean_ctor_set(v___x_2324_, 11, v___x_2304_);
lean_ctor_set(v___x_2324_, 12, v___x_2322_);
lean_ctor_set(v___x_2324_, 13, v___x_2323_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14, v___x_2305_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 1, v___x_2305_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 2, v___x_2305_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 3, v___x_2305_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 4, v___x_2305_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 5, v___x_2289_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 6, v___x_2289_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 7, v___x_2289_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 8, v___x_2305_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 9, v___x_2305_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 10, v___x_2289_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 11, v___x_2305_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 12, v___x_2289_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 13, v___x_2289_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 14, v___x_2289_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 15, v___x_2289_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 16, v___x_2289_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 17, v___x_2305_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 18, v___x_2289_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 19, v___x_2289_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 20, v___x_2289_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 21, v___x_2289_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 22, v___x_2289_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 23, v___x_2289_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 24, v___x_2289_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 25, v___x_2289_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 26, v___x_2289_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 27, v___x_2289_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 28, v___x_2289_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 29, v___x_2289_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 30, v___x_2305_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 31, v___x_2289_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*14 + 32, v___x_2289_);
v___x_2325_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_2324_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2328_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
lean_dec_ref_known(v___x_2325_, 1);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v_a_2312_);
v___x_2328_ = v___x_2302_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2312_);
v___x_2328_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___f_2332_; lean_object* v___x_2333_; 
v___x_2329_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v___x_2328_, v_a_2310_);
v___x_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2330_, 0, v_a_2314_);
v___x_2331_ = lean_box(v___x_2305_);
v___f_2332_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0___boxed), 13, 3);
lean_closure_set(v___f_2332_, 0, v___x_2330_);
lean_closure_set(v___f_2332_, 1, v___x_2331_);
lean_closure_set(v___f_2332_, 2, v___x_2329_);
v___x_2333_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___f_2332_, v_a_2326_, v___x_2323_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v_snd_2335_; lean_object* v_target_2336_; lean_object* v_hypotheses_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v_a_2340_; uint8_t v___x_2341_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2334_);
lean_dec_ref_known(v___x_2333_, 1);
v_snd_2335_ = lean_ctor_get(v_a_2334_, 1);
lean_inc(v_snd_2335_);
lean_dec(v_a_2334_);
v_target_2336_ = lean_ctor_get(v_snd_2335_, 2);
lean_inc_ref(v_target_2336_);
v_hypotheses_2337_ = lean_ctor_get(v_snd_2335_, 3);
lean_inc_ref(v_hypotheses_2337_);
lean_dec(v_snd_2335_);
v___x_2338_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_2336_);
lean_dec_ref(v_target_2336_);
v___x_2339_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(v___x_2338_, v___y_2297_);
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref(v___x_2339_);
v___x_2341_ = lean_unbox(v_a_2340_);
lean_dec(v_a_2340_);
if (v___x_2341_ == 0)
{
size_t v_sz_2342_; size_t v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v_sz_2342_ = lean_array_size(v_hypotheses_2337_);
v___x_2343_ = ((size_t)0ULL);
v___x_2344_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1(v_sz_2342_, v___x_2343_, v_hypotheses_2337_);
v___x_2345_ = l_Lean_MVarId_assertHypotheses(v___x_2338_, v___x_2344_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v_snd_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2356_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref_known(v___x_2345_, 1);
v_snd_2347_ = lean_ctor_get(v_a_2346_, 1);
v_isSharedCheck_2356_ = !lean_is_exclusive(v_a_2346_);
if (v_isSharedCheck_2356_ == 0)
{
lean_object* v_unused_2357_; 
v_unused_2357_ = lean_ctor_get(v_a_2346_, 0);
lean_dec(v_unused_2357_);
v___x_2349_ = v_a_2346_;
v_isShared_2350_ = v_isSharedCheck_2356_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_snd_2347_);
lean_dec(v_a_2346_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2356_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2351_; lean_object* v___x_2353_; 
v___x_2351_ = lean_box(0);
if (v_isShared_2350_ == 0)
{
lean_ctor_set_tag(v___x_2349_, 1);
lean_ctor_set(v___x_2349_, 1, v___x_2351_);
lean_ctor_set(v___x_2349_, 0, v_snd_2347_);
v___x_2353_ = v___x_2349_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_snd_2347_);
lean_ctor_set(v_reuseFailAlloc_2355_, 1, v___x_2351_);
v___x_2353_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
lean_object* v___x_2354_; 
v___x_2354_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2353_, v___y_2293_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
return v___x_2354_;
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
v_a_2358_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2345_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2345_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
lean_dec(v___x_2338_);
lean_dec_ref(v_hypotheses_2337_);
v___x_2366_ = lean_box(0);
v___x_2367_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2366_, v___y_2293_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
return v___x_2367_;
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
v_a_2368_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2333_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2333_);
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
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
lean_dec(v_a_2314_);
lean_dec(v_a_2312_);
lean_dec(v_a_2310_);
lean_del_object(v___x_2302_);
v_a_2377_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2325_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2325_);
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
lean_dec(v_a_2312_);
lean_dec(v_a_2310_);
lean_del_object(v___x_2302_);
v_a_2385_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2313_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2313_);
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
lean_dec(v_a_2310_);
lean_del_object(v___x_2302_);
v_a_2393_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2311_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2311_);
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
else
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
lean_del_object(v___x_2302_);
lean_dec(v_types_2291_);
v_a_2401_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2309_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2309_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2401_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
}
else
{
lean_dec(v_types_2291_);
lean_dec(v___x_2287_);
return v___x_2300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___boxed(lean_object* v_x_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Lean_Elab_Tactic_BVDecide_evalBVNormalize(v_x_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
lean_dec(v_a_2429_);
lean_dec_ref(v_a_2428_);
lean_dec(v_a_2427_);
lean_dec_ref(v_a_2426_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0(lean_object* v_mvarId_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(v_mvarId_2436_, v___y_2442_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___boxed(lean_object* v_mvarId_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0(v_mvarId_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v_mvarId_2447_);
return v_res_2457_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0(lean_object* v_00_u03b2_2458_, lean_object* v_x_2459_, lean_object* v_x_2460_){
_start:
{
uint8_t v___x_2461_; 
v___x_2461_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(v_x_2459_, v_x_2460_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2462_, lean_object* v_x_2463_, lean_object* v_x_2464_){
_start:
{
uint8_t v_res_2465_; lean_object* v_r_2466_; 
v_res_2465_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0(v_00_u03b2_2462_, v_x_2463_, v_x_2464_);
lean_dec(v_x_2464_);
lean_dec_ref(v_x_2463_);
v_r_2466_ = lean_box(v_res_2465_);
return v_r_2466_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2467_, lean_object* v_x_2468_, size_t v_x_2469_, lean_object* v_x_2470_){
_start:
{
uint8_t v___x_2471_; 
v___x_2471_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_2468_, v_x_2469_, v_x_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2472_, lean_object* v_x_2473_, lean_object* v_x_2474_, lean_object* v_x_2475_){
_start:
{
size_t v_x_3985__boxed_2476_; uint8_t v_res_2477_; lean_object* v_r_2478_; 
v_x_3985__boxed_2476_ = lean_unbox_usize(v_x_2474_);
lean_dec(v_x_2474_);
v_res_2477_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1(v_00_u03b2_2472_, v_x_2473_, v_x_3985__boxed_2476_, v_x_2475_);
lean_dec(v_x_2475_);
lean_dec_ref(v_x_2473_);
v_r_2478_ = lean_box(v_res_2477_);
return v_r_2478_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2479_, lean_object* v_keys_2480_, lean_object* v_vals_2481_, lean_object* v_heq_2482_, lean_object* v_i_2483_, lean_object* v_k_2484_){
_start:
{
uint8_t v___x_2485_; 
v___x_2485_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2480_, v_i_2483_, v_k_2484_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2486_, lean_object* v_keys_2487_, lean_object* v_vals_2488_, lean_object* v_heq_2489_, lean_object* v_i_2490_, lean_object* v_k_2491_){
_start:
{
uint8_t v_res_2492_; lean_object* v_r_2493_; 
v_res_2492_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2486_, v_keys_2487_, v_vals_2488_, v_heq_2489_, v_i_2490_, v_k_2491_);
lean_dec(v_k_2491_);
lean_dec_ref(v_vals_2488_);
lean_dec_ref(v_keys_2487_);
v_r_2493_ = lean_box(v_res_2492_);
return v_r_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1(){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2502_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2503_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0));
v___x_2504_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___closed__1));
v___x_2505_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___boxed), 10, 0);
v___x_2506_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2502_, v___x_2503_, v___x_2504_, v___x_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___boxed(lean_object* v_a_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1();
return v_res_2508_;
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
