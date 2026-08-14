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
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = lean_box(0);
v___x_423_ = lean_unsigned_to_nat(16u);
v___x_424_ = lean_mk_array(v___x_423_, v___x_422_);
return v___x_424_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_425_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3);
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
lean_ctor_set(v___x_427_, 1, v___x_425_);
return v___x_427_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4);
v___x_429_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
lean_ctor_set(v___x_429_, 2, v___x_428_);
lean_ctor_set(v___x_429_, 3, v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck(lean_object* v_target_432_, lean_object* v_ctx_433_, lean_object* v_warn_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___y_452_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_445_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2);
v___x_446_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5);
v___x_447_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6));
v___x_448_ = 0;
v___x_449_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_449_, 0, v___x_445_);
lean_ctor_set(v___x_449_, 1, v___x_446_);
lean_ctor_set(v___x_449_, 2, v_target_432_);
lean_ctor_set(v___x_449_, 3, v___x_447_);
lean_ctor_set_uint8(v___x_449_, sizeof(void*)*4, v___x_448_);
v___x_450_ = lean_st_mk_ref(v___x_449_);
lean_inc_ref(v_ctx_433_);
v___x_462_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_ctx_433_);
v___x_463_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_462_, v___x_450_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_);
lean_dec_ref(v___x_462_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; uint8_t v___x_465_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_a_464_);
lean_dec_ref_known(v___x_463_, 1);
v___x_465_ = lean_unbox(v_a_464_);
lean_dec(v_a_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v_target_468_; lean_object* v_hypotheses_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
lean_dec_ref(v_warn_434_);
v___x_466_ = lean_st_ref_get(v___x_450_);
v___x_467_ = lean_st_ref_get(v___x_450_);
v_target_468_ = lean_ctor_get(v___x_466_, 2);
lean_inc_ref(v_target_468_);
lean_dec(v___x_466_);
v_hypotheses_469_ = lean_ctor_get(v___x_467_, 3);
lean_inc_ref(v_hypotheses_469_);
lean_dec(v___x_467_);
v___x_470_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_468_);
lean_dec_ref(v_target_468_);
v___x_471_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(v___x_470_, v_hypotheses_469_, v_ctx_433_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_);
v___y_452_ = v___x_471_;
goto v___jp_451_;
}
else
{
lean_object* v___x_472_; 
lean_dec_ref(v_ctx_433_);
lean_inc(v_a_443_);
lean_inc_ref(v_a_442_);
lean_inc(v_a_441_);
lean_inc_ref(v_a_440_);
v___x_472_ = lean_apply_5(v_warn_434_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, lean_box(0));
v___y_452_ = v___x_472_;
goto v___jp_451_;
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_dec(v___x_450_);
lean_dec_ref(v_warn_434_);
lean_dec_ref(v_ctx_433_);
v_a_473_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_463_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_463_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
v___jp_451_:
{
if (lean_obj_tag(v___y_452_) == 0)
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_461_; 
v_a_453_ = lean_ctor_get(v___y_452_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___y_452_);
if (v_isSharedCheck_461_ == 0)
{
v___x_455_ = v___y_452_;
v_isShared_456_ = v_isSharedCheck_461_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___y_452_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_461_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v___x_459_; 
v___x_457_ = lean_st_ref_get(v___x_450_);
lean_dec(v___x_450_);
lean_dec(v___x_457_);
if (v_isShared_456_ == 0)
{
v___x_459_ = v___x_455_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_453_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
else
{
lean_dec(v___x_450_);
return v___y_452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed(lean_object* v_target_481_, lean_object* v_ctx_482_, lean_object* v_warn_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck(v_target_481_, v_ctx_482_, v_warn_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(lean_object* v___y_495_){
_start:
{
lean_object* v_ref_497_; uint8_t v___x_498_; lean_object* v___x_499_; 
v_ref_497_ = lean_ctor_get(v___y_495_, 5);
v___x_498_ = 0;
v___x_499_ = l_Lean_Syntax_getPos_x3f(v_ref_497_, v___x_498_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
return v___x_501_;
}
else
{
lean_object* v_val_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
v_val_502_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_499_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_val_502_);
lean_dec(v___x_499_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
lean_ctor_set_tag(v___x_504_, 0);
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_val_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg___boxed(lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v___y_510_);
lean_dec_ref(v___y_510_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0(lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v___y_517_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___boxed(lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0(v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
return v_res_528_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__2));
v___x_533_ = l_Lean_stringToMessageData(v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__4));
v___x_536_ = l_Lean_stringToMessageData(v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_fileName_544_; lean_object* v_fileMap_545_; lean_object* v___x_546_; 
v_fileName_544_ = lean_ctor_get(v_a_541_, 0);
v_fileMap_545_ = lean_ctor_get(v_a_541_, 1);
lean_inc_ref(v_fileName_544_);
v___x_546_ = l_System_FilePath_fileName(v_fileName_544_);
if (lean_obj_tag(v___x_546_) == 1)
{
lean_object* v_val_547_; lean_object* v___x_548_; 
v_val_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_val_547_);
lean_dec_ref_known(v___x_546_, 1);
v___x_548_ = l_Lean_Elab_Term_getDeclName_x3f___redArg(v_a_537_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v___x_548_, 1);
if (lean_obj_tag(v_a_549_) == 1)
{
lean_object* v_val_550_; lean_object* v___x_551_; lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_575_; 
v_val_550_ = lean_ctor_get(v_a_549_, 0);
lean_inc(v_val_550_);
lean_dec_ref_known(v_a_549_, 1);
v___x_551_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v_a_541_);
v_a_552_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_575_ == 0)
{
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_575_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_575_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v_line_557_; lean_object* v_column_558_; lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
lean_inc_ref(v_fileMap_545_);
v___x_556_ = l_Lean_FileMap_toPosition(v_fileMap_545_, v_a_552_);
lean_dec(v_a_552_);
v_line_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_line_557_);
v_column_558_ = lean_ctor_get(v___x_556_, 1);
lean_inc(v_column_558_);
lean_dec_ref(v___x_556_);
v___x_559_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__0));
v___x_560_ = lean_string_append(v_val_547_, v___x_559_);
v___x_561_ = 1;
v___x_562_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_550_, v___x_561_);
v___x_563_ = lean_string_append(v___x_560_, v___x_562_);
lean_dec_ref(v___x_562_);
v___x_564_ = lean_string_append(v___x_563_, v___x_559_);
v___x_565_ = l_Nat_reprFast(v_line_557_);
v___x_566_ = lean_string_append(v___x_564_, v___x_565_);
lean_dec_ref(v___x_565_);
v___x_567_ = lean_string_append(v___x_566_, v___x_559_);
v___x_568_ = l_Nat_reprFast(v_column_558_);
v___x_569_ = lean_string_append(v___x_567_, v___x_568_);
lean_dec_ref(v___x_568_);
v___x_570_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__1));
v___x_571_ = lean_string_append(v___x_569_, v___x_570_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_571_);
v___x_573_ = v___x_554_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v_a_549_);
lean_dec(v_val_547_);
v___x_576_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3, &l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3);
v___x_577_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v___x_576_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
return v___x_577_;
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
lean_dec(v_val_547_);
v_a_578_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_548_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_548_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec(v___x_546_);
v___x_586_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5, &l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5);
v___x_587_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v___x_586_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___boxed(lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(lean_object* v_cfg_596_, lean_object* v_types_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_606_; lean_object* v___x_607_; 
v_a_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_a_606_);
lean_dec_ref_known(v___x_605_, 1);
v___x_607_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v_a_606_, v_cfg_596_, v_types_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
return v___x_607_;
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_dec(v_types_597_);
lean_dec_ref(v_cfg_596_);
v_a_608_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_605_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_605_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext___boxed(lean_object* v_cfg_616_, lean_object* v_types_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(v_cfg_616_, v_types_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorIdx(lean_object* v_x_626_){
_start:
{
if (lean_obj_tag(v_x_626_) == 0)
{
lean_object* v___x_627_; 
v___x_627_ = lean_unsigned_to_nat(0u);
return v___x_627_;
}
else
{
lean_object* v___x_628_; 
v___x_628_ = lean_unsigned_to_nat(1u);
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorIdx___boxed(lean_object* v_x_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorIdx(v_x_629_);
lean_dec(v_x_629_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(lean_object* v_t_631_, lean_object* v_k_632_){
_start:
{
if (lean_obj_tag(v_t_631_) == 0)
{
return v_k_632_;
}
else
{
lean_object* v_path_633_; lean_object* v___x_634_; 
v_path_633_ = lean_ctor_get(v_t_631_, 0);
lean_inc_ref(v_path_633_);
lean_dec_ref_known(v_t_631_, 1);
v___x_634_ = lean_apply_1(v_k_632_, v_path_633_);
return v___x_634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim(lean_object* v_motive_635_, lean_object* v_ctorIdx_636_, lean_object* v_t_637_, lean_object* v_h_638_, lean_object* v_k_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_637_, v_k_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___boxed(lean_object* v_motive_641_, lean_object* v_ctorIdx_642_, lean_object* v_t_643_, lean_object* v_h_644_, lean_object* v_k_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim(v_motive_641_, v_ctorIdx_642_, v_t_643_, v_h_644_, v_k_645_);
lean_dec(v_ctorIdx_642_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_normalize_elim___redArg(lean_object* v_t_647_, lean_object* v_normalize_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_647_, v_normalize_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_normalize_elim(lean_object* v_motive_650_, lean_object* v_t_651_, lean_object* v_h_652_, lean_object* v_normalize_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_651_, v_normalize_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_check_elim___redArg(lean_object* v_t_655_, lean_object* v_check_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_655_, v_check_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_check_elim(lean_object* v_motive_658_, lean_object* v_t_659_, lean_object* v_h_660_, lean_object* v_check_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_TraceResult_ctorElim___redArg(v_t_659_, v_check_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0(lean_object* v_x_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v___x_674_; 
lean_inc(v___y_668_);
lean_inc_ref(v___y_667_);
lean_inc(v___y_666_);
lean_inc_ref(v___y_665_);
lean_inc(v___y_664_);
v___x_674_ = lean_apply_10(v_x_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, lean_box(0));
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0___boxed(lean_object* v_x_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0(v_x_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(lean_object* v_mvarId_687_, lean_object* v_x_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v___f_699_; lean_object* v___x_700_; 
lean_inc(v___y_693_);
lean_inc_ref(v___y_692_);
lean_inc(v___y_691_);
lean_inc_ref(v___y_690_);
lean_inc(v___y_689_);
v___f_699_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_699_, 0, v_x_688_);
lean_closure_set(v___f_699_, 1, v___y_689_);
lean_closure_set(v___f_699_, 2, v___y_690_);
lean_closure_set(v___f_699_, 3, v___y_691_);
lean_closure_set(v___f_699_, 4, v___y_692_);
lean_closure_set(v___f_699_, 5, v___y_693_);
v___x_700_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_687_, v___f_699_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
if (lean_obj_tag(v___x_700_) == 0)
{
return v___x_700_;
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___boxed(lean_object* v_mvarId_709_, lean_object* v_x_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v_mvarId_709_, v_x_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1(lean_object* v_00_u03b1_722_, lean_object* v_mvarId_723_, lean_object* v_x_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v_mvarId_723_, v_x_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___boxed(lean_object* v_00_u03b1_736_, lean_object* v_mvarId_737_, lean_object* v_x_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1(v_00_u03b1_736_, v_mvarId_737_, v_x_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(lean_object* v_e_750_){
_start:
{
if (lean_obj_tag(v_e_750_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_760_; 
v_a_752_ = lean_ctor_get(v_e_750_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v_e_750_);
if (v_isSharedCheck_760_ == 0)
{
v___x_754_ = v_e_750_;
v_isShared_755_ = v_isSharedCheck_760_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v_e_750_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_760_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v___x_758_; 
v___x_756_ = lean_mk_io_user_error(v_a_752_);
if (v_isShared_755_ == 0)
{
lean_ctor_set_tag(v___x_754_, 1);
lean_ctor_set(v___x_754_, 0, v___x_756_);
v___x_758_ = v___x_754_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
v_a_761_ = lean_ctor_get(v_e_750_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v_e_750_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v_e_750_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v_e_750_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set_tag(v___x_763_, 0);
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg___boxed(lean_object* v_e_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v_e_769_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2(lean_object* v_00_u03b1_772_, lean_object* v_e_773_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v_e_773_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___boxed(lean_object* v_00_u03b1_776_, lean_object* v_e_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2(v_00_u03b1_776_, v_e_777_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(lean_object* v_msg_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_ref_786_; lean_object* v___x_787_; lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_796_; 
v_ref_786_ = lean_ctor_get(v___y_783_, 5);
v___x_787_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v_msg_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_796_ == 0)
{
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_794_; 
lean_inc(v_ref_786_);
v___x_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_792_, 0, v_ref_786_);
lean_ctor_set(v___x_792_, 1, v_a_788_);
if (v_isShared_791_ == 0)
{
lean_ctor_set_tag(v___x_790_, 1);
lean_ctor_set(v___x_790_, 0, v___x_792_);
v___x_794_ = v___x_790_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg___boxed(lean_object* v_msg_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(v_msg_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(lean_object* v_target_804_, lean_object* v_ctx_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
lean_object* v_exprDef_816_; lean_object* v_certDef_817_; lean_object* v_reflectionDef_818_; lean_object* v_solver_819_; lean_object* v_lratPath_820_; lean_object* v_config_821_; lean_object* v_restrictedTypes_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_948_; 
v_exprDef_816_ = lean_ctor_get(v_ctx_805_, 0);
v_certDef_817_ = lean_ctor_get(v_ctx_805_, 1);
v_reflectionDef_818_ = lean_ctor_get(v_ctx_805_, 2);
v_solver_819_ = lean_ctor_get(v_ctx_805_, 3);
v_lratPath_820_ = lean_ctor_get(v_ctx_805_, 4);
v_config_821_ = lean_ctor_get(v_ctx_805_, 5);
v_restrictedTypes_822_ = lean_ctor_get(v_ctx_805_, 6);
v_isSharedCheck_948_ = !lean_is_exclusive(v_ctx_805_);
if (v_isSharedCheck_948_ == 0)
{
v___x_824_ = v_ctx_805_;
v_isShared_825_ = v_isSharedCheck_948_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_restrictedTypes_822_);
lean_inc(v_config_821_);
lean_inc(v_lratPath_820_);
lean_inc(v_solver_819_);
lean_inc(v_reflectionDef_818_);
lean_inc(v_certDef_817_);
lean_inc(v_exprDef_816_);
lean_dec(v_ctx_805_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_948_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v_timeout_848_; uint8_t v_trimProofs_849_; uint8_t v_binaryProofs_850_; uint8_t v_acNf_851_; uint8_t v_andFlattening_852_; uint8_t v_embeddedConstraintSubst_853_; uint8_t v_structures_854_; uint8_t v_fixedInt_855_; uint8_t v_enums_856_; uint8_t v_graphviz_857_; lean_object* v_maxSteps_858_; uint8_t v_shortCircuit_859_; uint8_t v_solverMode_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_947_; 
v_timeout_848_ = lean_ctor_get(v_config_821_, 0);
v_trimProofs_849_ = lean_ctor_get_uint8(v_config_821_, sizeof(void*)*2);
v_binaryProofs_850_ = lean_ctor_get_uint8(v_config_821_, sizeof(void*)*2 + 1);
v_acNf_851_ = lean_ctor_get_uint8(v_config_821_, sizeof(void*)*2 + 2);
v_andFlattening_852_ = lean_ctor_get_uint8(v_config_821_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_853_ = lean_ctor_get_uint8(v_config_821_, sizeof(void*)*2 + 4);
v_structures_854_ = lean_ctor_get_uint8(v_config_821_, sizeof(void*)*2 + 5);
v_fixedInt_855_ = lean_ctor_get_uint8(v_config_821_, sizeof(void*)*2 + 6);
v_enums_856_ = lean_ctor_get_uint8(v_config_821_, sizeof(void*)*2 + 7);
v_graphviz_857_ = lean_ctor_get_uint8(v_config_821_, sizeof(void*)*2 + 8);
v_maxSteps_858_ = lean_ctor_get(v_config_821_, 1);
v_shortCircuit_859_ = lean_ctor_get_uint8(v_config_821_, sizeof(void*)*2 + 9);
v_solverMode_860_ = lean_ctor_get_uint8(v_config_821_, sizeof(void*)*2 + 10);
v_isSharedCheck_947_ = !lean_is_exclusive(v_config_821_);
if (v_isSharedCheck_947_ == 0)
{
v___x_862_ = v_config_821_;
v_isShared_863_ = v_isSharedCheck_947_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_maxSteps_858_);
lean_inc(v_timeout_848_);
lean_dec(v_config_821_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_947_;
goto v_resetjp_861_;
}
v___jp_826_:
{
lean_object* v___x_836_; 
v___x_836_ = l_System_FilePath_fileName(v_lratPath_820_);
if (lean_obj_tag(v___x_836_) == 1)
{
lean_object* v_val_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_845_; 
v_val_837_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_845_ == 0)
{
v___x_839_ = v___x_836_;
v_isShared_840_ = v_isSharedCheck_845_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_val_837_);
lean_dec(v___x_836_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_845_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_val_837_);
v___x_842_ = v_reuseFailAlloc_844_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_843_; 
v___x_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
return v___x_843_;
}
}
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec(v___x_836_);
v___x_846_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5, &l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5);
v___x_847_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(v___x_846_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
return v___x_847_;
}
}
v_resetjp_861_:
{
lean_object* v___x_864_; uint8_t v___x_865_; lean_object* v___x_867_; 
v___x_864_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_804_);
v___x_865_ = 0;
if (v_isShared_863_ == 0)
{
v___x_867_ = v___x_862_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_timeout_848_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_maxSteps_858_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*2 + 1, v_binaryProofs_850_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*2 + 2, v_acNf_851_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*2 + 3, v_andFlattening_852_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_853_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*2 + 5, v_structures_854_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*2 + 6, v_fixedInt_855_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*2 + 7, v_enums_856_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*2 + 8, v_graphviz_857_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*2 + 9, v_shortCircuit_859_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*2 + 10, v_solverMode_860_);
v___x_867_ = v_reuseFailAlloc_946_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_869_; 
lean_ctor_set_uint8(v___x_867_, sizeof(void*)*2, v___x_865_);
lean_inc_ref(v_lratPath_820_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 5, v___x_867_);
v___x_869_ = v___x_824_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_exprDef_816_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_certDef_817_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v_reflectionDef_818_);
lean_ctor_set(v_reuseFailAlloc_945_, 3, v_solver_819_);
lean_ctor_set(v_reuseFailAlloc_945_, 4, v_lratPath_820_);
lean_ctor_set(v_reuseFailAlloc_945_, 5, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_945_, 6, v_restrictedTypes_822_);
v___x_869_ = v_reuseFailAlloc_945_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed), 12, 2);
lean_closure_set(v___x_870_, 0, v_target_804_);
lean_closure_set(v___x_870_, 1, v___x_869_);
v___x_871_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v___x_864_, v___x_870_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_936_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_936_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_936_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_936_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
if (lean_obj_tag(v_a_872_) == 0)
{
lean_object* v___x_876_; lean_object* v___x_878_; 
lean_dec_ref(v_lratPath_820_);
v___x_876_ = lean_box(0);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_876_);
v___x_878_ = v___x_874_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
else
{
lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_934_; 
lean_del_object(v___x_874_);
v_isSharedCheck_934_ = !lean_is_exclusive(v_a_872_);
if (v_isSharedCheck_934_ == 0)
{
lean_object* v_unused_935_; 
v_unused_935_ = lean_ctor_get(v_a_872_, 0);
lean_dec(v_unused_935_);
v___x_881_ = v_a_872_;
v_isShared_882_ = v_isSharedCheck_934_;
goto v_resetjp_880_;
}
else
{
lean_dec(v_a_872_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_934_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
if (v_trimProofs_849_ == 0)
{
lean_del_object(v___x_881_);
v___y_827_ = v_a_806_;
v___y_828_ = v_a_807_;
v___y_829_ = v_a_808_;
v___y_830_ = v_a_809_;
v___y_831_ = v_a_810_;
v___y_832_ = v_a_811_;
v___y_833_ = v_a_812_;
v___y_834_ = v_a_813_;
v___y_835_ = v_a_814_;
goto v___jp_826_;
}
else
{
lean_object* v___x_883_; 
v___x_883_ = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(v_lratPath_820_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
v___x_885_ = l_Lean_Meta_Tactic_BVDecide_LRAT_trim(v_a_884_);
lean_dec(v_a_884_);
v___x_886_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v___x_885_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v___x_888_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
lean_dec_ref_known(v___x_886_, 1);
v___x_888_ = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(v_lratPath_820_, v_a_887_, v_binaryProofs_850_);
lean_dec(v_a_887_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_dec_ref_known(v___x_888_, 1);
lean_del_object(v___x_881_);
v___y_827_ = v_a_806_;
v___y_828_ = v_a_807_;
v___y_829_ = v_a_808_;
v___y_830_ = v_a_809_;
v___y_831_ = v_a_810_;
v___y_832_ = v_a_811_;
v___y_833_ = v_a_812_;
v___y_834_ = v_a_813_;
v___y_835_ = v_a_814_;
goto v___jp_826_;
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_903_; 
lean_dec_ref(v_lratPath_820_);
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_903_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_903_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_903_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v_ref_893_; lean_object* v___x_894_; lean_object* v___x_896_; 
v_ref_893_ = lean_ctor_get(v_a_813_, 5);
v___x_894_ = lean_io_error_to_string(v_a_889_);
if (v_isShared_882_ == 0)
{
lean_ctor_set_tag(v___x_881_, 3);
lean_ctor_set(v___x_881_, 0, v___x_894_);
v___x_896_ = v___x_881_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_902_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_897_ = l_Lean_MessageData_ofFormat(v___x_896_);
lean_inc(v_ref_893_);
v___x_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_898_, 0, v_ref_893_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_898_);
v___x_900_ = v___x_891_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_918_; 
lean_dec_ref(v_lratPath_820_);
v_a_904_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_918_ == 0)
{
v___x_906_ = v___x_886_;
v_isShared_907_ = v_isSharedCheck_918_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_886_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_918_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v_ref_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
v_ref_908_ = lean_ctor_get(v_a_813_, 5);
v___x_909_ = lean_io_error_to_string(v_a_904_);
if (v_isShared_882_ == 0)
{
lean_ctor_set_tag(v___x_881_, 3);
lean_ctor_set(v___x_881_, 0, v___x_909_);
v___x_911_ = v___x_881_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_909_);
v___x_911_ = v_reuseFailAlloc_917_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_915_; 
v___x_912_ = l_Lean_MessageData_ofFormat(v___x_911_);
lean_inc(v_ref_908_);
v___x_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_913_, 0, v_ref_908_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v___x_913_);
v___x_915_ = v___x_906_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_913_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_933_; 
lean_dec_ref(v_lratPath_820_);
v_a_919_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_933_ == 0)
{
v___x_921_ = v___x_883_;
v_isShared_922_ = v_isSharedCheck_933_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_883_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_933_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v_ref_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
v_ref_923_ = lean_ctor_get(v_a_813_, 5);
v___x_924_ = lean_io_error_to_string(v_a_919_);
if (v_isShared_882_ == 0)
{
lean_ctor_set_tag(v___x_881_, 3);
lean_ctor_set(v___x_881_, 0, v___x_924_);
v___x_926_ = v___x_881_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_924_);
v___x_926_ = v_reuseFailAlloc_932_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_927_ = l_Lean_MessageData_ofFormat(v___x_926_);
lean_inc(v_ref_923_);
v___x_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_928_, 0, v_ref_923_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_928_);
v___x_930_ = v___x_921_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
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
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref(v_lratPath_820_);
v_a_937_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_871_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_871_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___boxed(lean_object* v_target_949_, lean_object* v_ctx_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(v_target_949_, v_ctx_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0(lean_object* v_00_u03b1_962_, lean_object* v_msg_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(v_msg_963_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___boxed(lean_object* v_00_u03b1_975_, lean_object* v_msg_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0(v_00_u03b1_975_, v_msg_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
return v_res_987_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_988_ = lean_box(0);
v___x_989_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
lean_ctor_set(v___x_990_, 1, v___x_988_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg(){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0);
v___x_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___boxed(lean_object* v___y_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0(lean_object* v_00_u03b1_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___boxed(lean_object* v_00_u03b1_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0(v_00_u03b1_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(lean_object* v_snd_1018_, lean_object* v___y_1019_, lean_object* v_a_x3f_1020_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_io_remove_file(v_snd_1018_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
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
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1043_; 
v_a_1031_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1033_ = v___x_1022_;
v_isShared_1034_ = v_isSharedCheck_1043_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1022_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1043_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v_ref_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v_ref_1035_ = lean_ctor_get(v___y_1019_, 5);
v___x_1036_ = lean_io_error_to_string(v_a_1031_);
v___x_1037_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
v___x_1038_ = l_Lean_MessageData_ofFormat(v___x_1037_);
lean_inc(v_ref_1035_);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v_ref_1035_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1039_);
v___x_1041_ = v___x_1033_;
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
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0___boxed(lean_object* v_snd_1044_, lean_object* v___y_1045_, lean_object* v_a_x3f_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_1044_, v___y_1045_, v_a_x3f_1046_);
lean_dec(v_a_x3f_1046_);
lean_dec_ref(v___y_1045_);
lean_dec_ref(v_snd_1044_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(lean_object* v_f_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v_fst_1061_; lean_object* v_snd_1062_; lean_object* v_r_1063_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1059_, 1);
v_fst_1061_ = lean_ctor_get(v_a_1060_, 0);
lean_inc(v_fst_1061_);
v_snd_1062_ = lean_ctor_get(v_a_1060_, 1);
lean_inc_n(v_snd_1062_, 2);
lean_dec(v_a_1060_);
lean_inc(v___y_1057_);
lean_inc_ref(v___y_1056_);
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
lean_inc(v___y_1051_);
lean_inc_ref(v___y_1050_);
v_r_1063_ = lean_apply_11(v_f_1049_, v_fst_1061_, v_snd_1062_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, lean_box(0));
if (lean_obj_tag(v_r_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1088_; 
v_a_1064_ = lean_ctor_get(v_r_1063_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_r_1063_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1066_ = v_r_1063_;
v_isShared_1067_ = v_isSharedCheck_1088_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v_r_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1088_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
lean_inc(v_a_1064_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 1);
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_1062_, v___y_1056_, v___x_1069_);
lean_dec_ref(v___x_1069_);
lean_dec(v_snd_1062_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1077_ == 0)
{
lean_object* v_unused_1078_; 
v_unused_1078_ = lean_ctor_get(v___x_1070_, 0);
lean_dec(v_unused_1078_);
v___x_1072_ = v___x_1070_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_dec(v___x_1070_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v_a_1064_);
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1064_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec(v_a_1064_);
v_a_1079_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1070_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1070_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v_a_1089_ = lean_ctor_get(v_r_1063_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v_r_1063_, 1);
v___x_1090_ = lean_box(0);
v___x_1091_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_1062_, v___y_1056_, v___x_1090_);
lean_dec(v_snd_1062_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1098_ == 0)
{
lean_object* v_unused_1099_; 
v_unused_1099_ = lean_ctor_get(v___x_1091_, 0);
lean_dec(v_unused_1099_);
v___x_1093_ = v___x_1091_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_dec(v___x_1091_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
lean_ctor_set_tag(v___x_1093_, 1);
lean_ctor_set(v___x_1093_, 0, v_a_1089_);
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1089_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec(v_a_1089_);
v_a_1100_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1091_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1091_);
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
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1120_; 
lean_dec_ref(v_f_1049_);
v_a_1108_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1110_ = v___x_1059_;
v_isShared_1111_ = v_isSharedCheck_1120_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1059_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1120_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v_ref_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
v_ref_1112_ = lean_ctor_get(v___y_1056_, 5);
v___x_1113_ = lean_io_error_to_string(v_a_1108_);
v___x_1114_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
v___x_1115_ = l_Lean_MessageData_ofFormat(v___x_1114_);
lean_inc(v_ref_1112_);
v___x_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1116_, 0, v_ref_1112_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1116_);
v___x_1118_ = v___x_1110_;
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
lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_dec_ref_known(v___x_1186_, 1);
v___x_1187_ = lean_box(0);
v___x_1188_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1187_, v___y_1162_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1196_; 
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1196_ == 0)
{
lean_object* v_unused_1197_; 
v_unused_1197_ = lean_ctor_get(v___x_1188_, 0);
lean_dec(v_unused_1197_);
v___x_1190_ = v___x_1188_;
v_isShared_1191_ = v_isSharedCheck_1196_;
goto v_resetjp_1189_;
}
else
{
lean_dec(v___x_1188_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1196_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1192_ = lean_box(0);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1192_);
v___x_1194_ = v___x_1190_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
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
else
{
return v___x_1188_;
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
uint8_t v___x_6747__boxed_1236_; uint8_t v___x_6748__boxed_1237_; lean_object* v_res_1238_; 
v___x_6747__boxed_1236_ = lean_unbox(v___x_1222_);
v___x_6748__boxed_1237_ = lean_unbox(v___x_1223_);
v_res_1238_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0(v___x_6747__boxed_1236_, v___x_6748__boxed_1237_, v___x_1224_, v___x_1225_, v_a_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
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
uint8_t v___x_6898__boxed_1287_; uint8_t v___x_6899__boxed_1288_; lean_object* v_res_1289_; 
v___x_6898__boxed_1287_ = lean_unbox(v___x_1272_);
v___x_6899__boxed_1288_ = lean_unbox(v___x_1273_);
v_res_1289_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1(v_a_1270_, v_a_1271_, v___x_6898__boxed_1287_, v___x_6899__boxed_1288_, v___x_1274_, v___x_1275_, v_x_1276_, v_lratFile_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
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
lean_object* v___x_1373_; lean_object* v_types_1374_; lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1373_ = lean_unsigned_to_nat(0u);
v_types_1374_ = l_Lean_Syntax_getArg(v___x_1369_, v___x_1373_);
lean_dec(v___x_1369_);
v___x_1375_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_types_1374_);
v___x_1376_ = l_Lean_Syntax_isOfKind(v_types_1374_, v___x_1375_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; 
lean_dec(v_types_1374_);
lean_dec(v___x_1324_);
v___x_1377_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1377_;
}
else
{
lean_object* v___x_1378_; 
v___x_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1378_, 0, v_types_1374_);
v_types_1328_ = v___x_1378_;
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
lean_object* v___x_1379_; 
lean_dec(v___x_1369_);
v___x_1379_ = lean_box(0);
v_types_1328_ = v___x_1379_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvDecide___boxed(lean_object* v_x_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide(v_x_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_);
lean_dec(v_a_1388_);
lean_dec_ref(v_a_1387_);
lean_dec(v_a_1386_);
lean_dec_ref(v_a_1385_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1(){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1400_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1401_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3));
v___x_1402_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2));
v___x_1403_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___boxed), 10, 0);
v___x_1404_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1400_, v___x_1401_, v___x_1402_, v___x_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___boxed(lean_object* v_a_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1();
return v_res_1406_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Array_mkArray0(lean_box(0));
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0(lean_object* v___x_1419_, lean_object* v_a_1420_, uint8_t v___x_1421_, lean_object* v___x_1422_, lean_object* v___x_1423_, lean_object* v___x_1424_, lean_object* v___x_1425_, lean_object* v_tk_1426_, lean_object* v_typesStx_1427_, lean_object* v___x_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(v___x_1419_, v_a_1420_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
lean_dec_ref_known(v___x_1439_, 1);
if (lean_obj_tag(v_a_1440_) == 0)
{
lean_object* v_ref_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___y_1451_; 
v_ref_1441_ = lean_ctor_get(v___y_1436_, 5);
v___x_1442_ = l_Lean_SourceInfo_fromRef(v_ref_1441_, v___x_1421_);
v___x_1443_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__1));
v___x_1444_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__2));
v___x_1445_ = l_Lean_Name_mkStr4(v___x_1422_, v___x_1423_, v___x_1424_, v___x_1444_);
v___x_1446_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3));
lean_inc(v___x_1442_);
v___x_1447_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1442_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___x_1448_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5));
v___x_1449_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6);
if (lean_obj_tag(v_typesStx_1427_) == 1)
{
lean_object* v_val_1463_; lean_object* v___x_1464_; 
v_val_1463_ = lean_ctor_get(v_typesStx_1427_, 0);
lean_inc(v_val_1463_);
lean_dec_ref_known(v_typesStx_1427_, 1);
v___x_1464_ = l_Array_mkArray1___redArg(v_val_1463_);
v___y_1451_ = v___x_1464_;
goto v___jp_1450_;
}
else
{
lean_object* v___x_1465_; 
lean_dec(v_typesStx_1427_);
v___x_1465_ = lean_mk_empty_array_with_capacity(v___x_1428_);
v___y_1451_ = v___x_1465_;
goto v___jp_1450_;
}
v___jp_1450_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1452_ = l_Array_append___redArg(v___x_1449_, v___y_1451_);
lean_dec_ref(v___y_1451_);
lean_inc(v___x_1442_);
v___x_1453_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1442_);
lean_ctor_set(v___x_1453_, 1, v___x_1448_);
lean_ctor_set(v___x_1453_, 2, v___x_1452_);
v___x_1454_ = l_Lean_Syntax_node3(v___x_1442_, v___x_1445_, v___x_1447_, v___x_1425_, v___x_1453_);
v___x_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1443_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
v___x_1456_ = lean_box(0);
v___x_1457_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1455_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
lean_ctor_set(v___x_1457_, 2, v___x_1456_);
lean_ctor_set(v___x_1457_, 3, v___x_1456_);
lean_ctor_set(v___x_1457_, 4, v___x_1456_);
lean_ctor_set(v___x_1457_, 5, v___x_1456_);
lean_inc(v_ref_1441_);
v___x_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1458_, 0, v_ref_1441_);
v___x_1459_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__7));
v___x_1460_ = 4;
v___x_1461_ = l_Lean_MessageData_nil;
v___x_1462_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1426_, v___x_1457_, v___x_1458_, v___x_1459_, v___x_1456_, v___x_1460_, v___x_1461_, v___y_1436_, v___y_1437_);
return v___x_1462_;
}
}
else
{
lean_object* v_path_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1499_; 
v_path_1466_ = lean_ctor_get(v_a_1440_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_a_1440_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1468_ = v_a_1440_;
v_isShared_1469_ = v_isSharedCheck_1499_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_path_1466_);
lean_dec(v_a_1440_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1499_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v_ref_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___y_1480_; 
v_ref_1470_ = lean_ctor_get(v___y_1436_, 5);
v___x_1471_ = l_Lean_SourceInfo_fromRef(v_ref_1470_, v___x_1421_);
v___x_1472_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__1));
v___x_1473_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__8));
v___x_1474_ = l_Lean_Name_mkStr4(v___x_1422_, v___x_1423_, v___x_1424_, v___x_1473_);
v___x_1475_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__9));
lean_inc(v___x_1471_);
v___x_1476_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1471_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
v___x_1477_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5));
v___x_1478_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6);
if (lean_obj_tag(v_typesStx_1427_) == 1)
{
lean_object* v_val_1496_; lean_object* v___x_1497_; 
v_val_1496_ = lean_ctor_get(v_typesStx_1427_, 0);
lean_inc(v_val_1496_);
lean_dec_ref_known(v_typesStx_1427_, 1);
v___x_1497_ = l_Array_mkArray1___redArg(v_val_1496_);
v___y_1480_ = v___x_1497_;
goto v___jp_1479_;
}
else
{
lean_object* v___x_1498_; 
lean_dec(v_typesStx_1427_);
v___x_1498_ = lean_mk_empty_array_with_capacity(v___x_1428_);
v___y_1480_ = v___x_1498_;
goto v___jp_1479_;
}
v___jp_1479_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1490_; 
v___x_1481_ = l_Array_append___redArg(v___x_1478_, v___y_1480_);
lean_dec_ref(v___y_1480_);
lean_inc(v___x_1471_);
v___x_1482_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1471_);
lean_ctor_set(v___x_1482_, 1, v___x_1477_);
lean_ctor_set(v___x_1482_, 2, v___x_1481_);
v___x_1483_ = lean_box(2);
v___x_1484_ = l_Lean_Syntax_mkStrLit(v_path_1466_, v___x_1483_);
v___x_1485_ = l_Lean_Syntax_node4(v___x_1471_, v___x_1474_, v___x_1476_, v___x_1425_, v___x_1482_, v___x_1484_);
v___x_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1472_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = lean_box(0);
v___x_1488_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1486_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
lean_ctor_set(v___x_1488_, 2, v___x_1487_);
lean_ctor_set(v___x_1488_, 3, v___x_1487_);
lean_ctor_set(v___x_1488_, 4, v___x_1487_);
lean_ctor_set(v___x_1488_, 5, v___x_1487_);
lean_inc(v_ref_1470_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v_ref_1470_);
v___x_1490_ = v___x_1468_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_ref_1470_);
v___x_1490_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
lean_object* v___x_1491_; uint8_t v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1491_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__7));
v___x_1492_ = 4;
v___x_1493_ = l_Lean_MessageData_nil;
v___x_1494_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1426_, v___x_1488_, v___x_1490_, v___x_1491_, v___x_1487_, v___x_1492_, v___x_1493_, v___y_1436_, v___y_1437_);
return v___x_1494_;
}
}
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v_typesStx_1427_);
lean_dec(v_tk_1426_);
lean_dec(v___x_1425_);
lean_dec_ref(v___x_1424_);
lean_dec_ref(v___x_1423_);
lean_dec_ref(v___x_1422_);
v_a_1500_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1439_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1439_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___boxed(lean_object** _args){
lean_object* v___x_1508_ = _args[0];
lean_object* v_a_1509_ = _args[1];
lean_object* v___x_1510_ = _args[2];
lean_object* v___x_1511_ = _args[3];
lean_object* v___x_1512_ = _args[4];
lean_object* v___x_1513_ = _args[5];
lean_object* v___x_1514_ = _args[6];
lean_object* v_tk_1515_ = _args[7];
lean_object* v_typesStx_1516_ = _args[8];
lean_object* v___x_1517_ = _args[9];
lean_object* v___y_1518_ = _args[10];
lean_object* v___y_1519_ = _args[11];
lean_object* v___y_1520_ = _args[12];
lean_object* v___y_1521_ = _args[13];
lean_object* v___y_1522_ = _args[14];
lean_object* v___y_1523_ = _args[15];
lean_object* v___y_1524_ = _args[16];
lean_object* v___y_1525_ = _args[17];
lean_object* v___y_1526_ = _args[18];
lean_object* v___y_1527_ = _args[19];
_start:
{
uint8_t v___x_22051__boxed_1528_; lean_object* v_res_1529_; 
v___x_22051__boxed_1528_ = lean_unbox(v___x_1510_);
v_res_1529_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0(v___x_1508_, v_a_1509_, v___x_22051__boxed_1528_, v___x_1511_, v___x_1512_, v___x_1513_, v___x_1514_, v_tk_1515_, v_typesStx_1516_, v___x_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec(v___x_1517_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic(lean_object* v_x_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
v___x_1546_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0));
v___x_1547_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1));
v___x_1548_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1));
v___x_1549_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__1));
lean_inc(v_x_1536_);
v___x_1550_ = l_Lean_Syntax_isOfKind(v_x_1536_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; 
lean_dec(v_x_1536_);
v___x_1551_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1551_;
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; uint8_t v___x_1555_; 
v___x_1552_ = lean_unsigned_to_nat(1u);
v___x_1553_ = l_Lean_Syntax_getArg(v_x_1536_, v___x_1552_);
v___x_1554_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_1553_);
v___x_1555_ = l_Lean_Syntax_isOfKind(v___x_1553_, v___x_1554_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; 
lean_dec(v___x_1553_);
lean_dec(v_x_1536_);
v___x_1556_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1556_;
}
else
{
lean_object* v___x_1557_; lean_object* v_tk_1558_; lean_object* v_typesStx_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___x_1646_; lean_object* v___x_1647_; uint8_t v___x_1648_; 
v___x_1557_ = lean_unsigned_to_nat(0u);
v_tk_1558_ = l_Lean_Syntax_getArg(v_x_1536_, v___x_1557_);
v___x_1646_ = lean_unsigned_to_nat(2u);
v___x_1647_ = l_Lean_Syntax_getArg(v_x_1536_, v___x_1646_);
lean_dec(v_x_1536_);
v___x_1648_ = l_Lean_Syntax_isNone(v___x_1647_);
if (v___x_1648_ == 0)
{
uint8_t v___x_1649_; 
lean_inc(v___x_1647_);
v___x_1649_ = l_Lean_Syntax_matchesNull(v___x_1647_, v___x_1552_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; 
lean_dec(v___x_1647_);
lean_dec(v_tk_1558_);
lean_dec(v___x_1553_);
v___x_1650_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1650_;
}
else
{
lean_object* v_typesStx_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v_typesStx_1651_ = l_Lean_Syntax_getArg(v___x_1647_, v___x_1557_);
lean_dec(v___x_1647_);
v___x_1652_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_typesStx_1651_);
v___x_1653_ = l_Lean_Syntax_isOfKind(v_typesStx_1651_, v___x_1652_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; 
lean_dec(v_typesStx_1651_);
lean_dec(v_tk_1558_);
lean_dec(v___x_1553_);
v___x_1654_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1654_;
}
else
{
lean_object* v___x_1655_; 
v___x_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1655_, 0, v_typesStx_1651_);
v_typesStx_1560_ = v___x_1655_;
v___y_1561_ = v_a_1537_;
v___y_1562_ = v_a_1538_;
v___y_1563_ = v_a_1539_;
v___y_1564_ = v_a_1540_;
v___y_1565_ = v_a_1541_;
v___y_1566_ = v_a_1542_;
v___y_1567_ = v_a_1543_;
v___y_1568_ = v_a_1544_;
goto v___jp_1559_;
}
}
}
else
{
lean_object* v___x_1656_; 
lean_dec(v___x_1647_);
v___x_1656_ = lean_box(0);
v_typesStx_1560_ = v___x_1656_;
v___y_1561_ = v_a_1537_;
v___y_1562_ = v_a_1538_;
v___y_1563_ = v_a_1539_;
v___y_1564_ = v_a_1540_;
v___y_1565_ = v_a_1541_;
v___y_1566_ = v_a_1542_;
v___y_1567_ = v_a_1543_;
v___y_1568_ = v_a_1544_;
goto v___jp_1559_;
}
v___jp_1559_:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1567_, v___y_1568_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1644_; 
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1644_ == 0)
{
lean_object* v_unused_1645_; 
v_unused_1645_ = lean_ctor_get(v___x_1569_, 0);
lean_dec(v_unused_1645_);
v___x_1571_ = v___x_1569_;
v_isShared_1572_ = v_isSharedCheck_1644_;
goto v_resetjp_1570_;
}
else
{
lean_dec(v___x_1569_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1644_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; uint8_t v___x_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1573_ = lean_unsigned_to_nat(10u);
v___x_1574_ = 0;
v___x_1575_ = lean_unsigned_to_nat(100000u);
v___x_1576_ = 0;
v___x_1577_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_1577_, 0, v___x_1573_);
lean_ctor_set(v___x_1577_, 1, v___x_1575_);
lean_ctor_set_uint8(v___x_1577_, sizeof(void*)*2, v___x_1555_);
lean_ctor_set_uint8(v___x_1577_, sizeof(void*)*2 + 1, v___x_1555_);
lean_ctor_set_uint8(v___x_1577_, sizeof(void*)*2 + 2, v___x_1574_);
lean_ctor_set_uint8(v___x_1577_, sizeof(void*)*2 + 3, v___x_1555_);
lean_ctor_set_uint8(v___x_1577_, sizeof(void*)*2 + 4, v___x_1555_);
lean_ctor_set_uint8(v___x_1577_, sizeof(void*)*2 + 5, v___x_1555_);
lean_ctor_set_uint8(v___x_1577_, sizeof(void*)*2 + 6, v___x_1555_);
lean_ctor_set_uint8(v___x_1577_, sizeof(void*)*2 + 7, v___x_1555_);
lean_ctor_set_uint8(v___x_1577_, sizeof(void*)*2 + 8, v___x_1574_);
lean_ctor_set_uint8(v___x_1577_, sizeof(void*)*2 + 9, v___x_1574_);
lean_ctor_set_uint8(v___x_1577_, sizeof(void*)*2 + 10, v___x_1576_);
lean_inc(v___x_1553_);
v___x_1578_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_1553_, v___x_1577_, v___x_1555_, v___y_1561_, v___y_1567_, v___y_1568_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v___x_1580_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v___x_1578_, 1);
lean_inc(v_typesStx_1560_);
v___x_1580_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_1560_, v_a_1579_, v___y_1567_, v___y_1568_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1582_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v___x_1580_, 1);
v___x_1582_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(v_a_1579_, v_a_1581_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v___x_1584_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1562_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1586_ = lean_unsigned_to_nat(9u);
v___x_1587_ = lean_unsigned_to_nat(5u);
v___x_1588_ = lean_unsigned_to_nat(8u);
v___x_1589_ = lean_unsigned_to_nat(1000u);
v___x_1590_ = lean_unsigned_to_nat(1024u);
v___x_1591_ = lean_unsigned_to_nat(10000u);
v___x_1592_ = lean_unsigned_to_nat(1048576u);
v___x_1593_ = lean_unsigned_to_nat(50u);
v___x_1594_ = lean_box(0);
v___x_1595_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_1595_, 0, v___x_1586_);
lean_ctor_set(v___x_1595_, 1, v___x_1587_);
lean_ctor_set(v___x_1595_, 2, v___x_1588_);
lean_ctor_set(v___x_1595_, 3, v___x_1588_);
lean_ctor_set(v___x_1595_, 4, v___x_1589_);
lean_ctor_set(v___x_1595_, 5, v___x_1589_);
lean_ctor_set(v___x_1595_, 6, v___x_1575_);
lean_ctor_set(v___x_1595_, 7, v___x_1590_);
lean_ctor_set(v___x_1595_, 8, v___x_1591_);
lean_ctor_set(v___x_1595_, 9, v___x_1589_);
lean_ctor_set(v___x_1595_, 10, v___x_1592_);
lean_ctor_set(v___x_1595_, 11, v___x_1573_);
lean_ctor_set(v___x_1595_, 12, v___x_1593_);
lean_ctor_set(v___x_1595_, 13, v___x_1594_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14, v___x_1574_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 1, v___x_1574_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 2, v___x_1574_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 3, v___x_1574_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 4, v___x_1574_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 5, v___x_1555_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 6, v___x_1555_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 7, v___x_1555_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 8, v___x_1574_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 9, v___x_1574_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 10, v___x_1555_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 11, v___x_1574_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 12, v___x_1555_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 13, v___x_1555_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 14, v___x_1555_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 15, v___x_1555_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 16, v___x_1555_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 17, v___x_1574_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 18, v___x_1555_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 19, v___x_1555_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 20, v___x_1555_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 21, v___x_1555_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 22, v___x_1555_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 23, v___x_1555_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 24, v___x_1555_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 25, v___x_1555_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 26, v___x_1555_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 27, v___x_1555_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 28, v___x_1555_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 29, v___x_1555_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 30, v___x_1574_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 31, v___x_1555_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*14 + 32, v___x_1555_);
v___x_1596_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_1595_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; lean_object* v___x_1599_; 
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_a_1597_);
lean_dec_ref_known(v___x_1596_, 1);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 0, v_a_1585_);
v___x_1599_ = v___x_1571_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1585_);
v___x_1599_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1600_; lean_object* v___f_1601_; lean_object* v___x_1602_; 
v___x_1600_ = lean_box(v___x_1574_);
v___f_1601_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___boxed), 20, 10);
lean_closure_set(v___f_1601_, 0, v___x_1599_);
lean_closure_set(v___f_1601_, 1, v_a_1583_);
lean_closure_set(v___f_1601_, 2, v___x_1600_);
lean_closure_set(v___f_1601_, 3, v___x_1546_);
lean_closure_set(v___f_1601_, 4, v___x_1547_);
lean_closure_set(v___f_1601_, 5, v___x_1548_);
lean_closure_set(v___f_1601_, 6, v___x_1553_);
lean_closure_set(v___f_1601_, 7, v_tk_1558_);
lean_closure_set(v___f_1601_, 8, v_typesStx_1560_);
lean_closure_set(v___f_1601_, 9, v___x_1557_);
v___x_1602_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___f_1601_, v_a_1597_, v___x_1594_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
return v___x_1602_;
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec(v_a_1585_);
lean_dec(v_a_1583_);
lean_del_object(v___x_1571_);
lean_dec(v_typesStx_1560_);
lean_dec(v_tk_1558_);
lean_dec(v___x_1553_);
v_a_1604_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1596_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1596_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec(v_a_1583_);
lean_del_object(v___x_1571_);
lean_dec(v_typesStx_1560_);
lean_dec(v_tk_1558_);
lean_dec(v___x_1553_);
v_a_1612_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1584_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1584_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_del_object(v___x_1571_);
lean_dec(v_typesStx_1560_);
lean_dec(v_tk_1558_);
lean_dec(v___x_1553_);
v_a_1620_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1582_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1582_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
lean_dec(v_a_1579_);
lean_del_object(v___x_1571_);
lean_dec(v_typesStx_1560_);
lean_dec(v_tk_1558_);
lean_dec(v___x_1553_);
v_a_1628_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1580_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1580_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_del_object(v___x_1571_);
lean_dec(v_typesStx_1560_);
lean_dec(v_tk_1558_);
lean_dec(v___x_1553_);
v_a_1636_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1578_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1578_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
}
else
{
lean_dec(v_typesStx_1560_);
lean_dec(v_tk_1558_);
lean_dec(v___x_1553_);
return v___x_1569_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___boxed(lean_object* v_x_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic(v_x_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_);
lean_dec(v_a_1665_);
lean_dec_ref(v_a_1664_);
lean_dec(v_a_1663_);
lean_dec_ref(v_a_1662_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
lean_dec(v_a_1659_);
lean_dec_ref(v_a_1658_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1(){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1676_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1677_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___closed__1));
v___x_1678_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___closed__1));
v___x_1679_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___boxed), 10, 0);
v___x_1680_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1676_, v___x_1677_, v___x_1678_, v___x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1___boxed(lean_object* v_a_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic__1();
return v_res_1682_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_1689_, uint8_t v_suppressElabErrors_1690_, lean_object* v_x_1691_){
_start:
{
if (lean_obj_tag(v_x_1691_) == 1)
{
lean_object* v_pre_1692_; 
v_pre_1692_ = lean_ctor_get(v_x_1691_, 0);
switch(lean_obj_tag(v_pre_1692_))
{
case 1:
{
lean_object* v_pre_1693_; 
v_pre_1693_ = lean_ctor_get(v_pre_1692_, 0);
switch(lean_obj_tag(v_pre_1693_))
{
case 0:
{
lean_object* v_str_1694_; lean_object* v_str_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; 
v_str_1694_ = lean_ctor_get(v_x_1691_, 1);
v_str_1695_ = lean_ctor_get(v_pre_1692_, 1);
v___x_1696_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__0));
v___x_1697_ = lean_string_dec_eq(v_str_1695_, v___x_1696_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; uint8_t v___x_1699_; 
v___x_1698_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1));
v___x_1699_ = lean_string_dec_eq(v_str_1695_, v___x_1698_);
if (v___x_1699_ == 0)
{
return v___y_1689_;
}
else
{
lean_object* v___x_1700_; uint8_t v___x_1701_; 
v___x_1700_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_1701_ = lean_string_dec_eq(v_str_1694_, v___x_1700_);
if (v___x_1701_ == 0)
{
return v___y_1689_;
}
else
{
return v_suppressElabErrors_1690_;
}
}
}
else
{
lean_object* v___x_1702_; uint8_t v___x_1703_; 
v___x_1702_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_1703_ = lean_string_dec_eq(v_str_1694_, v___x_1702_);
if (v___x_1703_ == 0)
{
return v___y_1689_;
}
else
{
return v_suppressElabErrors_1690_;
}
}
}
case 1:
{
lean_object* v_pre_1704_; 
v_pre_1704_ = lean_ctor_get(v_pre_1693_, 0);
if (lean_obj_tag(v_pre_1704_) == 0)
{
lean_object* v_str_1705_; lean_object* v_str_1706_; lean_object* v_str_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v_str_1705_ = lean_ctor_get(v_x_1691_, 1);
v_str_1706_ = lean_ctor_get(v_pre_1692_, 1);
v_str_1707_ = lean_ctor_get(v_pre_1693_, 1);
v___x_1708_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_1709_ = lean_string_dec_eq(v_str_1707_, v___x_1708_);
if (v___x_1709_ == 0)
{
return v___y_1689_;
}
else
{
lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1710_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_1711_ = lean_string_dec_eq(v_str_1706_, v___x_1710_);
if (v___x_1711_ == 0)
{
return v___y_1689_;
}
else
{
lean_object* v___x_1712_; uint8_t v___x_1713_; 
v___x_1712_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_1713_ = lean_string_dec_eq(v_str_1705_, v___x_1712_);
if (v___x_1713_ == 0)
{
return v___y_1689_;
}
else
{
return v_suppressElabErrors_1690_;
}
}
}
}
else
{
return v___y_1689_;
}
}
default: 
{
return v___y_1689_;
}
}
}
case 0:
{
lean_object* v_str_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; 
v_str_1714_ = lean_ctor_get(v_x_1691_, 1);
v___x_1715_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_1716_ = lean_string_dec_eq(v_str_1714_, v___x_1715_);
if (v___x_1716_ == 0)
{
return v___y_1689_;
}
else
{
return v_suppressElabErrors_1690_;
}
}
default: 
{
return v___y_1689_;
}
}
}
else
{
return v___y_1689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_1717_, lean_object* v_suppressElabErrors_1718_, lean_object* v_x_1719_){
_start:
{
uint8_t v___y_8349__boxed_1720_; uint8_t v_suppressElabErrors_boxed_1721_; uint8_t v_res_1722_; lean_object* v_r_1723_; 
v___y_8349__boxed_1720_ = lean_unbox(v___y_1717_);
v_suppressElabErrors_boxed_1721_ = lean_unbox(v_suppressElabErrors_1718_);
v_res_1722_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0(v___y_8349__boxed_1720_, v_suppressElabErrors_boxed_1721_, v_x_1719_);
lean_dec(v_x_1719_);
v_r_1723_ = lean_box(v_res_1722_);
return v_r_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(lean_object* v_ref_1725_, lean_object* v_msgData_1726_, uint8_t v_severity_1727_, uint8_t v_isSilent_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v___y_1735_; uint8_t v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; uint8_t v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1771_; uint8_t v___y_1772_; lean_object* v___y_1773_; uint8_t v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; uint8_t v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1796_; lean_object* v___y_1797_; uint8_t v___y_1798_; uint8_t v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; uint8_t v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1807_; uint8_t v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; uint8_t v___y_1812_; uint8_t v___y_1813_; uint8_t v___x_1818_; lean_object* v___y_1820_; uint8_t v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; uint8_t v___y_1825_; uint8_t v___y_1826_; uint8_t v___y_1828_; uint8_t v___x_1843_; 
v___x_1818_ = 2;
v___x_1843_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1727_, v___x_1818_);
if (v___x_1843_ == 0)
{
v___y_1828_ = v___x_1843_;
goto v___jp_1827_;
}
else
{
uint8_t v___x_1844_; 
lean_inc_ref(v_msgData_1726_);
v___x_1844_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1726_);
v___y_1828_ = v___x_1844_;
goto v___jp_1827_;
}
v___jp_1734_:
{
lean_object* v___x_1744_; lean_object* v_currNamespace_1745_; lean_object* v_openDecls_1746_; lean_object* v_env_1747_; lean_object* v_nextMacroScope_1748_; lean_object* v_ngen_1749_; lean_object* v_auxDeclNGen_1750_; lean_object* v_traceState_1751_; lean_object* v_cache_1752_; lean_object* v_messages_1753_; lean_object* v_infoState_1754_; lean_object* v_snapshotTasks_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1769_; 
v___x_1744_ = lean_st_ref_take(v___y_1743_);
v_currNamespace_1745_ = lean_ctor_get(v___y_1742_, 6);
v_openDecls_1746_ = lean_ctor_get(v___y_1742_, 7);
v_env_1747_ = lean_ctor_get(v___x_1744_, 0);
v_nextMacroScope_1748_ = lean_ctor_get(v___x_1744_, 1);
v_ngen_1749_ = lean_ctor_get(v___x_1744_, 2);
v_auxDeclNGen_1750_ = lean_ctor_get(v___x_1744_, 3);
v_traceState_1751_ = lean_ctor_get(v___x_1744_, 4);
v_cache_1752_ = lean_ctor_get(v___x_1744_, 5);
v_messages_1753_ = lean_ctor_get(v___x_1744_, 6);
v_infoState_1754_ = lean_ctor_get(v___x_1744_, 7);
v_snapshotTasks_1755_ = lean_ctor_get(v___x_1744_, 8);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1757_ = v___x_1744_;
v_isShared_1758_ = v_isSharedCheck_1769_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_snapshotTasks_1755_);
lean_inc(v_infoState_1754_);
lean_inc(v_messages_1753_);
lean_inc(v_cache_1752_);
lean_inc(v_traceState_1751_);
lean_inc(v_auxDeclNGen_1750_);
lean_inc(v_ngen_1749_);
lean_inc(v_nextMacroScope_1748_);
lean_inc(v_env_1747_);
lean_dec(v___x_1744_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1769_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1764_; 
lean_inc(v_openDecls_1746_);
lean_inc(v_currNamespace_1745_);
v___x_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1759_, 0, v_currNamespace_1745_);
lean_ctor_set(v___x_1759_, 1, v_openDecls_1746_);
v___x_1760_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
lean_ctor_set(v___x_1760_, 1, v___y_1735_);
lean_inc_ref(v___y_1737_);
lean_inc_ref(v___y_1738_);
v___x_1761_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1761_, 0, v___y_1738_);
lean_ctor_set(v___x_1761_, 1, v___y_1740_);
lean_ctor_set(v___x_1761_, 2, v___y_1739_);
lean_ctor_set(v___x_1761_, 3, v___y_1737_);
lean_ctor_set(v___x_1761_, 4, v___x_1760_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*5, v___y_1741_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*5 + 1, v___y_1736_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*5 + 2, v_isSilent_1728_);
v___x_1762_ = l_Lean_MessageLog_add(v___x_1761_, v_messages_1753_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 6, v___x_1762_);
v___x_1764_ = v___x_1757_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_env_1747_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_nextMacroScope_1748_);
lean_ctor_set(v_reuseFailAlloc_1768_, 2, v_ngen_1749_);
lean_ctor_set(v_reuseFailAlloc_1768_, 3, v_auxDeclNGen_1750_);
lean_ctor_set(v_reuseFailAlloc_1768_, 4, v_traceState_1751_);
lean_ctor_set(v_reuseFailAlloc_1768_, 5, v_cache_1752_);
lean_ctor_set(v_reuseFailAlloc_1768_, 6, v___x_1762_);
lean_ctor_set(v_reuseFailAlloc_1768_, 7, v_infoState_1754_);
lean_ctor_set(v_reuseFailAlloc_1768_, 8, v_snapshotTasks_1755_);
v___x_1764_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1765_ = lean_st_ref_put(v___y_1743_, v___x_1764_);
v___x_1766_ = lean_box(0);
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
return v___x_1767_;
}
}
}
v___jp_1770_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1794_; 
v___x_1779_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1726_);
v___x_1780_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v___x_1779_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1783_ = v___x_1780_;
v_isShared_1784_ = v_isSharedCheck_1794_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1780_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1794_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
lean_inc_ref_n(v___y_1773_, 2);
v___x_1785_ = l_Lean_FileMap_toPosition(v___y_1773_, v___y_1775_);
lean_dec(v___y_1775_);
v___x_1786_ = l_Lean_FileMap_toPosition(v___y_1773_, v___y_1778_);
lean_dec(v___y_1778_);
v___x_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
v___x_1788_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___closed__0));
if (v___y_1772_ == 0)
{
lean_del_object(v___x_1783_);
lean_dec_ref(v___y_1771_);
v___y_1735_ = v_a_1781_;
v___y_1736_ = v___y_1774_;
v___y_1737_ = v___x_1788_;
v___y_1738_ = v___y_1776_;
v___y_1739_ = v___x_1787_;
v___y_1740_ = v___x_1785_;
v___y_1741_ = v___y_1777_;
v___y_1742_ = v___y_1731_;
v___y_1743_ = v___y_1732_;
goto v___jp_1734_;
}
else
{
uint8_t v___x_1789_; 
lean_inc(v_a_1781_);
v___x_1789_ = l_Lean_MessageData_hasTag(v___y_1771_, v_a_1781_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; lean_object* v___x_1792_; 
lean_dec_ref_known(v___x_1787_, 1);
lean_dec_ref(v___x_1785_);
lean_dec(v_a_1781_);
v___x_1790_ = lean_box(0);
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 0, v___x_1790_);
v___x_1792_ = v___x_1783_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
else
{
lean_del_object(v___x_1783_);
v___y_1735_ = v_a_1781_;
v___y_1736_ = v___y_1774_;
v___y_1737_ = v___x_1788_;
v___y_1738_ = v___y_1776_;
v___y_1739_ = v___x_1787_;
v___y_1740_ = v___x_1785_;
v___y_1741_ = v___y_1777_;
v___y_1742_ = v___y_1731_;
v___y_1743_ = v___y_1732_;
goto v___jp_1734_;
}
}
}
}
v___jp_1795_:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Lean_Syntax_getTailPos_x3f(v___y_1801_, v___y_1802_);
lean_dec(v___y_1801_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_inc(v___y_1803_);
v___y_1771_ = v___y_1796_;
v___y_1772_ = v___y_1798_;
v___y_1773_ = v___y_1797_;
v___y_1774_ = v___y_1799_;
v___y_1775_ = v___y_1803_;
v___y_1776_ = v___y_1800_;
v___y_1777_ = v___y_1802_;
v___y_1778_ = v___y_1803_;
goto v___jp_1770_;
}
else
{
lean_object* v_val_1805_; 
v_val_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_val_1805_);
lean_dec_ref_known(v___x_1804_, 1);
v___y_1771_ = v___y_1796_;
v___y_1772_ = v___y_1798_;
v___y_1773_ = v___y_1797_;
v___y_1774_ = v___y_1799_;
v___y_1775_ = v___y_1803_;
v___y_1776_ = v___y_1800_;
v___y_1777_ = v___y_1802_;
v___y_1778_ = v_val_1805_;
goto v___jp_1770_;
}
}
v___jp_1806_:
{
lean_object* v_ref_1814_; lean_object* v___x_1815_; 
v_ref_1814_ = l_Lean_replaceRef(v_ref_1725_, v___y_1811_);
v___x_1815_ = l_Lean_Syntax_getPos_x3f(v_ref_1814_, v___y_1812_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v___x_1816_; 
v___x_1816_ = lean_unsigned_to_nat(0u);
v___y_1796_ = v___y_1807_;
v___y_1797_ = v___y_1809_;
v___y_1798_ = v___y_1808_;
v___y_1799_ = v___y_1813_;
v___y_1800_ = v___y_1810_;
v___y_1801_ = v_ref_1814_;
v___y_1802_ = v___y_1812_;
v___y_1803_ = v___x_1816_;
goto v___jp_1795_;
}
else
{
lean_object* v_val_1817_; 
v_val_1817_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_val_1817_);
lean_dec_ref_known(v___x_1815_, 1);
v___y_1796_ = v___y_1807_;
v___y_1797_ = v___y_1809_;
v___y_1798_ = v___y_1808_;
v___y_1799_ = v___y_1813_;
v___y_1800_ = v___y_1810_;
v___y_1801_ = v_ref_1814_;
v___y_1802_ = v___y_1812_;
v___y_1803_ = v_val_1817_;
goto v___jp_1795_;
}
}
v___jp_1819_:
{
if (v___y_1826_ == 0)
{
v___y_1807_ = v___y_1824_;
v___y_1808_ = v___y_1821_;
v___y_1809_ = v___y_1820_;
v___y_1810_ = v___y_1822_;
v___y_1811_ = v___y_1823_;
v___y_1812_ = v___y_1825_;
v___y_1813_ = v_severity_1727_;
goto v___jp_1806_;
}
else
{
v___y_1807_ = v___y_1824_;
v___y_1808_ = v___y_1821_;
v___y_1809_ = v___y_1820_;
v___y_1810_ = v___y_1822_;
v___y_1811_ = v___y_1823_;
v___y_1812_ = v___y_1825_;
v___y_1813_ = v___x_1818_;
goto v___jp_1806_;
}
}
v___jp_1827_:
{
if (v___y_1828_ == 0)
{
lean_object* v_fileName_1829_; lean_object* v_fileMap_1830_; lean_object* v_options_1831_; lean_object* v_ref_1832_; uint8_t v_suppressElabErrors_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___f_1836_; uint8_t v___x_1837_; uint8_t v___x_1838_; 
v_fileName_1829_ = lean_ctor_get(v___y_1731_, 0);
v_fileMap_1830_ = lean_ctor_get(v___y_1731_, 1);
v_options_1831_ = lean_ctor_get(v___y_1731_, 2);
v_ref_1832_ = lean_ctor_get(v___y_1731_, 5);
v_suppressElabErrors_1833_ = lean_ctor_get_uint8(v___y_1731_, sizeof(void*)*14 + 1);
v___x_1834_ = lean_box(v___y_1828_);
v___x_1835_ = lean_box(v_suppressElabErrors_1833_);
v___f_1836_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1836_, 0, v___x_1834_);
lean_closure_set(v___f_1836_, 1, v___x_1835_);
v___x_1837_ = 1;
v___x_1838_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1727_, v___x_1837_);
if (v___x_1838_ == 0)
{
v___y_1820_ = v_fileMap_1830_;
v___y_1821_ = v_suppressElabErrors_1833_;
v___y_1822_ = v_fileName_1829_;
v___y_1823_ = v_ref_1832_;
v___y_1824_ = v___f_1836_;
v___y_1825_ = v___y_1828_;
v___y_1826_ = v___x_1838_;
goto v___jp_1819_;
}
else
{
lean_object* v___x_1839_; uint8_t v___x_1840_; 
v___x_1839_ = l_Lean_warningAsError;
v___x_1840_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_1831_, v___x_1839_);
v___y_1820_ = v_fileMap_1830_;
v___y_1821_ = v_suppressElabErrors_1833_;
v___y_1822_ = v_fileName_1829_;
v___y_1823_ = v_ref_1832_;
v___y_1824_ = v___f_1836_;
v___y_1825_ = v___y_1828_;
v___y_1826_ = v___x_1840_;
goto v___jp_1819_;
}
}
else
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
lean_dec_ref(v_msgData_1726_);
v___x_1841_ = lean_box(0);
v___x_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
return v___x_1842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_1845_, lean_object* v_msgData_1846_, lean_object* v_severity_1847_, lean_object* v_isSilent_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
uint8_t v_severity_boxed_1854_; uint8_t v_isSilent_boxed_1855_; lean_object* v_res_1856_; 
v_severity_boxed_1854_ = lean_unbox(v_severity_1847_);
v_isSilent_boxed_1855_ = lean_unbox(v_isSilent_1848_);
v_res_1856_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(v_ref_1845_, v_msgData_1846_, v_severity_boxed_1854_, v_isSilent_boxed_1855_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v_ref_1845_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(lean_object* v_msgData_1857_, uint8_t v_severity_1858_, uint8_t v_isSilent_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_ref_1865_; lean_object* v___x_1866_; 
v_ref_1865_ = lean_ctor_get(v___y_1862_, 5);
v___x_1866_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0_spec__1(v_ref_1865_, v_msgData_1857_, v_severity_1858_, v_isSilent_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0___boxed(lean_object* v_msgData_1867_, lean_object* v_severity_1868_, lean_object* v_isSilent_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
uint8_t v_severity_boxed_1875_; uint8_t v_isSilent_boxed_1876_; lean_object* v_res_1877_; 
v_severity_boxed_1875_ = lean_unbox(v_severity_1868_);
v_isSilent_boxed_1876_ = lean_unbox(v_isSilent_1869_);
v_res_1877_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(v_msgData_1867_, v_severity_boxed_1875_, v_isSilent_boxed_1876_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(lean_object* v_msgData_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
uint8_t v___x_1884_; uint8_t v___x_1885_; lean_object* v___x_1886_; 
v___x_1884_ = 1;
v___x_1885_ = 0;
v___x_1886_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0_spec__0(v_msgData_1878_, v___x_1884_, v___x_1885_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0___boxed(lean_object* v_msgData_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(v_msgData_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
return v_res_1893_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__0));
v___x_1896_ = l_Lean_stringToMessageData(v___x_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0(uint8_t v___x_1897_, lean_object* v___x_1898_, lean_object* v___x_1899_, lean_object* v___x_1900_, lean_object* v___x_1901_, lean_object* v_tk_1902_, lean_object* v_typesStx_1903_, lean_object* v___x_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_ref_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___y_1920_; 
v_ref_1910_ = lean_ctor_get(v___y_1907_, 5);
v___x_1911_ = l_Lean_SourceInfo_fromRef(v_ref_1910_, v___x_1897_);
v___x_1912_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__1));
v___x_1913_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__2));
v___x_1914_ = l_Lean_Name_mkStr4(v___x_1898_, v___x_1899_, v___x_1900_, v___x_1913_);
v___x_1915_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__3));
lean_inc(v___x_1911_);
v___x_1916_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1911_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__5));
v___x_1918_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__6);
if (lean_obj_tag(v_typesStx_1903_) == 1)
{
lean_object* v_val_1941_; lean_object* v___x_1942_; 
v_val_1941_ = lean_ctor_get(v_typesStx_1903_, 0);
lean_inc(v_val_1941_);
lean_dec_ref_known(v_typesStx_1903_, 1);
v___x_1942_ = l_Array_mkArray1___redArg(v_val_1941_);
v___y_1920_ = v___x_1942_;
goto v___jp_1919_;
}
else
{
lean_object* v___x_1943_; 
lean_dec(v_typesStx_1903_);
v___x_1943_ = lean_mk_empty_array_with_capacity(v___x_1904_);
v___y_1920_ = v___x_1943_;
goto v___jp_1919_;
}
v___jp_1919_:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1, &l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___closed__1);
v___x_1922_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_evalBvCheckTactic_spec__0(v___x_1921_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1939_; 
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1939_ == 0)
{
lean_object* v_unused_1940_; 
v_unused_1940_ = lean_ctor_get(v___x_1922_, 0);
lean_dec(v_unused_1940_);
v___x_1924_ = v___x_1922_;
v_isShared_1925_ = v_isSharedCheck_1939_;
goto v_resetjp_1923_;
}
else
{
lean_dec(v___x_1922_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1939_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1926_ = l_Array_append___redArg(v___x_1918_, v___y_1920_);
lean_dec_ref(v___y_1920_);
lean_inc(v___x_1911_);
v___x_1927_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1911_);
lean_ctor_set(v___x_1927_, 1, v___x_1917_);
lean_ctor_set(v___x_1927_, 2, v___x_1926_);
v___x_1928_ = l_Lean_Syntax_node3(v___x_1911_, v___x_1914_, v___x_1916_, v___x_1901_, v___x_1927_);
v___x_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1912_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = lean_box(0);
v___x_1931_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
lean_ctor_set(v___x_1931_, 2, v___x_1930_);
lean_ctor_set(v___x_1931_, 3, v___x_1930_);
lean_ctor_set(v___x_1931_, 4, v___x_1930_);
lean_ctor_set(v___x_1931_, 5, v___x_1930_);
lean_inc(v_ref_1910_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set_tag(v___x_1924_, 1);
lean_ctor_set(v___x_1924_, 0, v_ref_1910_);
v___x_1933_ = v___x_1924_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_ref_1910_);
v___x_1933_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1934_; uint8_t v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1934_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvTraceTactic___lam__0___closed__7));
v___x_1935_ = 4;
v___x_1936_ = l_Lean_MessageData_nil;
v___x_1937_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1902_, v___x_1931_, v___x_1933_, v___x_1934_, v___x_1930_, v___x_1935_, v___x_1936_, v___y_1907_, v___y_1908_);
return v___x_1937_;
}
}
}
else
{
lean_dec_ref(v___y_1920_);
lean_dec_ref_known(v___x_1916_, 2);
lean_dec(v___x_1914_);
lean_dec(v___x_1911_);
lean_dec(v_tk_1902_);
lean_dec(v___x_1901_);
return v___x_1922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___boxed(lean_object* v___x_1944_, lean_object* v___x_1945_, lean_object* v___x_1946_, lean_object* v___x_1947_, lean_object* v___x_1948_, lean_object* v_tk_1949_, lean_object* v_typesStx_1950_, lean_object* v___x_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
uint8_t v___x_8680__boxed_1957_; lean_object* v_res_1958_; 
v___x_8680__boxed_1957_ = lean_unbox(v___x_1944_);
v_res_1958_ = l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0(v___x_8680__boxed_1957_, v___x_1945_, v___x_1946_, v___x_1947_, v___x_1948_, v_tk_1949_, v_typesStx_1950_, v___x_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___x_1951_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic(lean_object* v_x_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; 
v___x_1977_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0));
v___x_1978_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1));
v___x_1979_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_ensureBvDecide___closed__1));
v___x_1980_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0));
lean_inc(v_x_1967_);
v___x_1981_ = l_Lean_Syntax_isOfKind(v_x_1967_, v___x_1980_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; 
lean_dec(v_x_1967_);
v___x_1982_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1982_;
}
else
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
v___x_1983_ = lean_unsigned_to_nat(1u);
v___x_1984_ = l_Lean_Syntax_getArg(v_x_1967_, v___x_1983_);
v___x_1985_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_1984_);
v___x_1986_ = l_Lean_Syntax_isOfKind(v___x_1984_, v___x_1985_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; 
lean_dec(v___x_1984_);
lean_dec(v_x_1967_);
v___x_1987_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_1987_;
}
else
{
lean_object* v___x_1988_; lean_object* v_tk_1989_; lean_object* v_typesStx_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___x_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_1988_ = lean_unsigned_to_nat(0u);
v_tk_1989_ = l_Lean_Syntax_getArg(v_x_1967_, v___x_1988_);
v___x_2084_ = lean_unsigned_to_nat(2u);
v___x_2085_ = l_Lean_Syntax_getArg(v_x_1967_, v___x_2084_);
v___x_2086_ = l_Lean_Syntax_isNone(v___x_2085_);
if (v___x_2086_ == 0)
{
uint8_t v___x_2087_; 
lean_inc(v___x_2085_);
v___x_2087_ = l_Lean_Syntax_matchesNull(v___x_2085_, v___x_1983_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; 
lean_dec(v___x_2085_);
lean_dec(v_tk_1989_);
lean_dec(v___x_1984_);
lean_dec(v_x_1967_);
v___x_2088_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2088_;
}
else
{
lean_object* v_typesStx_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; 
v_typesStx_2089_ = l_Lean_Syntax_getArg(v___x_2085_, v___x_1988_);
lean_dec(v___x_2085_);
v___x_2090_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_typesStx_2089_);
v___x_2091_ = l_Lean_Syntax_isOfKind(v_typesStx_2089_, v___x_2090_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; 
lean_dec(v_typesStx_2089_);
lean_dec(v_tk_1989_);
lean_dec(v___x_1984_);
lean_dec(v_x_1967_);
v___x_2092_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2092_;
}
else
{
lean_object* v___x_2093_; 
v___x_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_typesStx_2089_);
v_typesStx_1991_ = v___x_2093_;
v___y_1992_ = v_a_1968_;
v___y_1993_ = v_a_1969_;
v___y_1994_ = v_a_1970_;
v___y_1995_ = v_a_1971_;
v___y_1996_ = v_a_1972_;
v___y_1997_ = v_a_1973_;
v___y_1998_ = v_a_1974_;
v___y_1999_ = v_a_1975_;
goto v___jp_1990_;
}
}
}
else
{
lean_object* v___x_2094_; 
lean_dec(v___x_2085_);
v___x_2094_ = lean_box(0);
v_typesStx_1991_ = v___x_2094_;
v___y_1992_ = v_a_1968_;
v___y_1993_ = v_a_1969_;
v___y_1994_ = v_a_1970_;
v___y_1995_ = v_a_1971_;
v___y_1996_ = v_a_1972_;
v___y_1997_ = v_a_1973_;
v___y_1998_ = v_a_1974_;
v___y_1999_ = v_a_1975_;
goto v___jp_1990_;
}
v___jp_1990_:
{
lean_object* v___x_2000_; lean_object* v_path_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v___x_2000_ = lean_unsigned_to_nat(3u);
v_path_2001_ = l_Lean_Syntax_getArg(v_x_1967_, v___x_2000_);
lean_dec(v_x_1967_);
v___x_2002_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__2));
lean_inc(v_path_2001_);
v___x_2003_ = l_Lean_Syntax_isOfKind(v_path_2001_, v___x_2002_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; 
lean_dec(v_path_2001_);
lean_dec(v_typesStx_1991_);
lean_dec(v_tk_1989_);
lean_dec(v___x_1984_);
v___x_2004_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2004_;
}
else
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2082_; 
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2082_ == 0)
{
lean_object* v_unused_2083_; 
v_unused_2083_ = lean_ctor_get(v___x_2005_, 0);
lean_dec(v_unused_2083_);
v___x_2007_ = v___x_2005_;
v_isShared_2008_ = v_isSharedCheck_2082_;
goto v_resetjp_2006_;
}
else
{
lean_dec(v___x_2005_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2082_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2009_; uint8_t v___x_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2009_ = lean_unsigned_to_nat(10u);
v___x_2010_ = 0;
v___x_2011_ = lean_unsigned_to_nat(100000u);
v___x_2012_ = 0;
v___x_2013_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_2013_, 0, v___x_2009_);
lean_ctor_set(v___x_2013_, 1, v___x_2011_);
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*2, v___x_1986_);
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*2 + 1, v___x_1986_);
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*2 + 2, v___x_2010_);
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*2 + 3, v___x_1986_);
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*2 + 4, v___x_1986_);
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*2 + 5, v___x_1986_);
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*2 + 6, v___x_1986_);
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*2 + 7, v___x_1986_);
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*2 + 8, v___x_2010_);
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*2 + 9, v___x_2010_);
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*2 + 10, v___x_2012_);
lean_inc(v___x_1984_);
v___x_2014_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_1984_, v___x_2013_, v___x_1986_, v___y_1992_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2016_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2014_, 1);
lean_inc(v_typesStx_1991_);
v___x_2016_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_1991_, v_a_2015_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref_known(v___x_2016_, 1);
v___x_2018_ = l_Lean_TSyntax_getString(v_path_2001_);
lean_dec(v_path_2001_);
v___x_2019_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v___x_2018_, v_a_2015_, v_a_2017_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2021_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2019_, 1);
v___x_2021_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1993_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___x_2021_, 1);
v___x_2023_ = lean_unsigned_to_nat(9u);
v___x_2024_ = lean_unsigned_to_nat(5u);
v___x_2025_ = lean_unsigned_to_nat(8u);
v___x_2026_ = lean_unsigned_to_nat(1000u);
v___x_2027_ = lean_unsigned_to_nat(1024u);
v___x_2028_ = lean_unsigned_to_nat(10000u);
v___x_2029_ = lean_unsigned_to_nat(1048576u);
v___x_2030_ = lean_unsigned_to_nat(50u);
v___x_2031_ = lean_box(0);
v___x_2032_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_2032_, 0, v___x_2023_);
lean_ctor_set(v___x_2032_, 1, v___x_2024_);
lean_ctor_set(v___x_2032_, 2, v___x_2025_);
lean_ctor_set(v___x_2032_, 3, v___x_2025_);
lean_ctor_set(v___x_2032_, 4, v___x_2026_);
lean_ctor_set(v___x_2032_, 5, v___x_2026_);
lean_ctor_set(v___x_2032_, 6, v___x_2011_);
lean_ctor_set(v___x_2032_, 7, v___x_2027_);
lean_ctor_set(v___x_2032_, 8, v___x_2028_);
lean_ctor_set(v___x_2032_, 9, v___x_2026_);
lean_ctor_set(v___x_2032_, 10, v___x_2029_);
lean_ctor_set(v___x_2032_, 11, v___x_2009_);
lean_ctor_set(v___x_2032_, 12, v___x_2030_);
lean_ctor_set(v___x_2032_, 13, v___x_2031_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14, v___x_2010_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 1, v___x_2010_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 2, v___x_2010_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 3, v___x_2010_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 4, v___x_2010_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 5, v___x_1986_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 6, v___x_1986_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 7, v___x_1986_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 8, v___x_2010_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 9, v___x_2010_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 10, v___x_1986_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 11, v___x_2010_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 12, v___x_1986_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 13, v___x_1986_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 14, v___x_1986_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 15, v___x_1986_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 16, v___x_1986_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 17, v___x_2010_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 18, v___x_1986_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 19, v___x_1986_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 20, v___x_1986_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 21, v___x_1986_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 22, v___x_1986_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 23, v___x_1986_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 24, v___x_1986_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 25, v___x_1986_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 26, v___x_1986_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 27, v___x_1986_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 28, v___x_1986_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 29, v___x_1986_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 30, v___x_2010_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 31, v___x_1986_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*14 + 32, v___x_1986_);
v___x_2033_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_2032_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2035_; lean_object* v___f_2036_; lean_object* v___x_2038_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref_known(v___x_2033_, 1);
v___x_2035_ = lean_box(v___x_2010_);
v___f_2036_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___lam__0___boxed), 13, 8);
lean_closure_set(v___f_2036_, 0, v___x_2035_);
lean_closure_set(v___f_2036_, 1, v___x_1977_);
lean_closure_set(v___f_2036_, 2, v___x_1978_);
lean_closure_set(v___f_2036_, 3, v___x_1979_);
lean_closure_set(v___f_2036_, 4, v___x_1984_);
lean_closure_set(v___f_2036_, 5, v_tk_1989_);
lean_closure_set(v___f_2036_, 6, v_typesStx_1991_);
lean_closure_set(v___f_2036_, 7, v___x_1988_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v_a_2022_);
v___x_2038_ = v___x_2007_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2022_);
v___x_2038_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2039_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed), 13, 3);
lean_closure_set(v___x_2039_, 0, v___x_2038_);
lean_closure_set(v___x_2039_, 1, v_a_2020_);
lean_closure_set(v___x_2039_, 2, v___f_2036_);
v___x_2040_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___x_2039_, v_a_2034_, v___x_2031_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
return v___x_2040_;
}
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec(v_a_2022_);
lean_dec(v_a_2020_);
lean_del_object(v___x_2007_);
lean_dec(v_typesStx_1991_);
lean_dec(v_tk_1989_);
lean_dec(v___x_1984_);
v_a_2042_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2033_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2033_);
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
lean_dec(v_a_2020_);
lean_del_object(v___x_2007_);
lean_dec(v_typesStx_1991_);
lean_dec(v_tk_1989_);
lean_dec(v___x_1984_);
v_a_2050_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2021_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2021_);
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
lean_del_object(v___x_2007_);
lean_dec(v_typesStx_1991_);
lean_dec(v_tk_1989_);
lean_dec(v___x_1984_);
v_a_2058_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2019_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2019_);
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
lean_dec(v_a_2015_);
lean_del_object(v___x_2007_);
lean_dec(v_path_2001_);
lean_dec(v_typesStx_1991_);
lean_dec(v_tk_1989_);
lean_dec(v___x_1984_);
v_a_2066_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2016_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2016_);
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
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_del_object(v___x_2007_);
lean_dec(v_path_2001_);
lean_dec(v_typesStx_1991_);
lean_dec(v_tk_1989_);
lean_dec(v___x_1984_);
v_a_2074_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2014_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2014_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
}
else
{
lean_dec(v_path_2001_);
lean_dec(v_typesStx_1991_);
lean_dec(v_tk_1989_);
lean_dec(v___x_1984_);
return v___x_2005_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___boxed(lean_object* v_x_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic(v_x_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
lean_dec(v_a_2103_);
lean_dec_ref(v_a_2102_);
lean_dec(v_a_2101_);
lean_dec_ref(v_a_2100_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
lean_dec(v_a_2097_);
lean_dec_ref(v_a_2096_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1(){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2114_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2115_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___closed__0));
v___x_2116_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___closed__1));
v___x_2117_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___boxed), 10, 0);
v___x_2118_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2114_, v___x_2115_, v___x_2116_, v___x_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1___boxed(lean_object* v_a_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvCheckTactic___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvCheckTactic__1();
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0(lean_object* v___x_2121_, uint8_t v___x_2122_, lean_object* v___x_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2134_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2);
v___x_2135_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5);
v___x_2136_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6));
v___x_2137_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2137_, 0, v___x_2134_);
lean_ctor_set(v___x_2137_, 1, v___x_2135_);
lean_ctor_set(v___x_2137_, 2, v___x_2121_);
lean_ctor_set(v___x_2137_, 3, v___x_2136_);
lean_ctor_set_uint8(v___x_2137_, sizeof(void*)*4, v___x_2122_);
v___x_2138_ = lean_st_mk_ref(v___x_2137_);
v___x_2139_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_2123_, v___x_2138_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2149_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2142_ = v___x_2139_;
v_isShared_2143_ = v_isSharedCheck_2149_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2139_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2149_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2147_; 
v___x_2144_ = lean_st_ref_get(v___x_2138_);
lean_dec(v___x_2138_);
v___x_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2145_, 0, v_a_2140_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v___x_2145_);
v___x_2147_ = v___x_2142_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
lean_dec(v___x_2138_);
v_a_2150_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2139_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2139_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0___boxed(lean_object* v___x_2158_, lean_object* v___x_2159_, lean_object* v___x_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
uint8_t v___x_4604__boxed_2171_; lean_object* v_res_2172_; 
v___x_4604__boxed_2171_ = lean_unbox(v___x_2159_);
v_res_2172_ = l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0(v___x_2158_, v___x_4604__boxed_2171_, v___x_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___x_2160_);
return v_res_2172_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_2173_, lean_object* v_i_2174_, lean_object* v_k_2175_){
_start:
{
lean_object* v___x_2176_; uint8_t v___x_2177_; 
v___x_2176_ = lean_array_get_size(v_keys_2173_);
v___x_2177_ = lean_nat_dec_lt(v_i_2174_, v___x_2176_);
if (v___x_2177_ == 0)
{
lean_dec(v_i_2174_);
return v___x_2177_;
}
else
{
lean_object* v_k_x27_2178_; uint8_t v___x_2179_; 
v_k_x27_2178_ = lean_array_fget_borrowed(v_keys_2173_, v_i_2174_);
v___x_2179_ = l_Lean_instBEqMVarId_beq(v_k_2175_, v_k_x27_2178_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = lean_unsigned_to_nat(1u);
v___x_2181_ = lean_nat_add(v_i_2174_, v___x_2180_);
lean_dec(v_i_2174_);
v_i_2174_ = v___x_2181_;
goto _start;
}
else
{
lean_dec(v_i_2174_);
return v___x_2179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_2183_, lean_object* v_i_2184_, lean_object* v_k_2185_){
_start:
{
uint8_t v_res_2186_; lean_object* v_r_2187_; 
v_res_2186_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2183_, v_i_2184_, v_k_2185_);
lean_dec(v_k_2185_);
lean_dec_ref(v_keys_2183_);
v_r_2187_ = lean_box(v_res_2186_);
return v_r_2187_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2188_, size_t v_x_2189_, lean_object* v_x_2190_){
_start:
{
if (lean_obj_tag(v_x_2188_) == 0)
{
lean_object* v_es_2191_; lean_object* v___x_2192_; size_t v___x_2193_; size_t v___x_2194_; lean_object* v_j_2195_; lean_object* v___x_2196_; 
v_es_2191_ = lean_ctor_get(v_x_2188_, 0);
v___x_2192_ = lean_box(2);
v___x_2193_ = ((size_t)31ULL);
v___x_2194_ = lean_usize_land(v_x_2189_, v___x_2193_);
v_j_2195_ = lean_usize_to_nat(v___x_2194_);
v___x_2196_ = lean_array_get_borrowed(v___x_2192_, v_es_2191_, v_j_2195_);
lean_dec(v_j_2195_);
switch(lean_obj_tag(v___x_2196_))
{
case 0:
{
lean_object* v_key_2197_; uint8_t v___x_2198_; 
v_key_2197_ = lean_ctor_get(v___x_2196_, 0);
v___x_2198_ = l_Lean_instBEqMVarId_beq(v_x_2190_, v_key_2197_);
return v___x_2198_;
}
case 1:
{
lean_object* v_node_2199_; size_t v___x_2200_; size_t v___x_2201_; 
v_node_2199_ = lean_ctor_get(v___x_2196_, 0);
v___x_2200_ = ((size_t)5ULL);
v___x_2201_ = lean_usize_shift_right(v_x_2189_, v___x_2200_);
v_x_2188_ = v_node_2199_;
v_x_2189_ = v___x_2201_;
goto _start;
}
default: 
{
uint8_t v___x_2203_; 
v___x_2203_ = 0;
return v___x_2203_;
}
}
}
else
{
lean_object* v_ks_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; 
v_ks_2204_ = lean_ctor_get(v_x_2188_, 0);
v___x_2205_ = lean_unsigned_to_nat(0u);
v___x_2206_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_2204_, v___x_2205_, v_x_2190_);
return v___x_2206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2207_, lean_object* v_x_2208_, lean_object* v_x_2209_){
_start:
{
size_t v_x_4710__boxed_2210_; uint8_t v_res_2211_; lean_object* v_r_2212_; 
v_x_4710__boxed_2210_ = lean_unbox_usize(v_x_2208_);
lean_dec(v_x_2208_);
v_res_2211_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_2207_, v_x_4710__boxed_2210_, v_x_2209_);
lean_dec(v_x_2209_);
lean_dec_ref(v_x_2207_);
v_r_2212_ = lean_box(v_res_2211_);
return v_r_2212_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(lean_object* v_x_2213_, lean_object* v_x_2214_){
_start:
{
uint64_t v___x_2215_; size_t v___x_2216_; uint8_t v___x_2217_; 
v___x_2215_ = l_Lean_instHashableMVarId_hash(v_x_2214_);
v___x_2216_ = lean_uint64_to_usize(v___x_2215_);
v___x_2217_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_2213_, v___x_2216_, v_x_2214_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_2218_, lean_object* v_x_2219_){
_start:
{
uint8_t v_res_2220_; lean_object* v_r_2221_; 
v_res_2220_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(v_x_2218_, v_x_2219_);
lean_dec(v_x_2219_);
lean_dec_ref(v_x_2218_);
v_r_2221_ = lean_box(v_res_2220_);
return v_r_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(lean_object* v_mvarId_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v___x_2225_; lean_object* v_mctx_2226_; lean_object* v_eAssignment_2227_; uint8_t v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2225_ = lean_st_ref_get(v___y_2223_);
v_mctx_2226_ = lean_ctor_get(v___x_2225_, 0);
lean_inc_ref(v_mctx_2226_);
lean_dec(v___x_2225_);
v_eAssignment_2227_ = lean_ctor_get(v_mctx_2226_, 8);
lean_inc_ref(v_eAssignment_2227_);
lean_dec_ref(v_mctx_2226_);
v___x_2228_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(v_eAssignment_2227_, v_mvarId_2222_);
lean_dec_ref(v_eAssignment_2227_);
v___x_2229_ = lean_box(v___x_2228_);
v___x_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg___boxed(lean_object* v_mvarId_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(v_mvarId_2231_, v___y_2232_);
lean_dec(v___y_2232_);
lean_dec(v_mvarId_2231_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1(size_t v_sz_2235_, size_t v_i_2236_, lean_object* v_bs_2237_){
_start:
{
uint8_t v___x_2238_; 
v___x_2238_ = lean_usize_dec_lt(v_i_2236_, v_sz_2235_);
if (v___x_2238_ == 0)
{
return v_bs_2237_;
}
else
{
lean_object* v_v_2239_; lean_object* v_name_2240_; lean_object* v_type_2241_; lean_object* v_value_2242_; lean_object* v___x_2243_; lean_object* v_bs_x27_2244_; uint8_t v___x_2245_; uint8_t v___x_2246_; lean_object* v___x_2247_; size_t v___x_2248_; size_t v___x_2249_; lean_object* v___x_2250_; 
v_v_2239_ = lean_array_uget_borrowed(v_bs_2237_, v_i_2236_);
v_name_2240_ = lean_ctor_get(v_v_2239_, 0);
lean_inc(v_name_2240_);
v_type_2241_ = lean_ctor_get(v_v_2239_, 1);
lean_inc_ref(v_type_2241_);
v_value_2242_ = lean_ctor_get(v_v_2239_, 2);
lean_inc_ref(v_value_2242_);
v___x_2243_ = lean_unsigned_to_nat(0u);
v_bs_x27_2244_ = lean_array_uset(v_bs_2237_, v_i_2236_, v___x_2243_);
v___x_2245_ = 0;
v___x_2246_ = 0;
v___x_2247_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2247_, 0, v_name_2240_);
lean_ctor_set(v___x_2247_, 1, v_type_2241_);
lean_ctor_set(v___x_2247_, 2, v_value_2242_);
lean_ctor_set_uint8(v___x_2247_, sizeof(void*)*3, v___x_2245_);
lean_ctor_set_uint8(v___x_2247_, sizeof(void*)*3 + 1, v___x_2246_);
v___x_2248_ = ((size_t)1ULL);
v___x_2249_ = lean_usize_add(v_i_2236_, v___x_2248_);
v___x_2250_ = lean_array_uset(v_bs_x27_2244_, v_i_2236_, v___x_2247_);
v_i_2236_ = v___x_2249_;
v_bs_2237_ = v___x_2250_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1___boxed(lean_object* v_sz_2252_, lean_object* v_i_2253_, lean_object* v_bs_2254_){
_start:
{
size_t v_sz_boxed_2255_; size_t v_i_boxed_2256_; lean_object* v_res_2257_; 
v_sz_boxed_2255_ = lean_unbox_usize(v_sz_2252_);
lean_dec(v_sz_2252_);
v_i_boxed_2256_ = lean_unbox_usize(v_i_2253_);
lean_dec(v_i_2253_);
v_res_2257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1(v_sz_boxed_2255_, v_i_boxed_2256_, v_bs_2254_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize(lean_object* v_x_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v___x_2273_; uint8_t v___x_2274_; 
v___x_2273_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0));
lean_inc(v_x_2263_);
v___x_2274_ = l_Lean_Syntax_isOfKind(v_x_2263_, v___x_2273_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2275_; 
lean_dec(v_x_2263_);
v___x_2275_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2275_;
}
else
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; uint8_t v___x_2279_; lean_object* v_types_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; 
v___x_2276_ = lean_unsigned_to_nat(1u);
v___x_2277_ = l_Lean_Syntax_getArg(v_x_2263_, v___x_2276_);
v___x_2278_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5));
lean_inc(v___x_2277_);
v___x_2279_ = l_Lean_Syntax_isOfKind(v___x_2277_, v___x_2278_);
if (v___x_2279_ == 0)
{
lean_object* v___x_2401_; 
lean_dec(v___x_2277_);
lean_dec(v_x_2263_);
v___x_2401_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2401_;
}
else
{
lean_object* v___x_2402_; lean_object* v___x_2403_; uint8_t v___x_2404_; 
v___x_2402_ = lean_unsigned_to_nat(2u);
v___x_2403_ = l_Lean_Syntax_getArg(v_x_2263_, v___x_2402_);
lean_dec(v_x_2263_);
v___x_2404_ = l_Lean_Syntax_isNone(v___x_2403_);
if (v___x_2404_ == 0)
{
uint8_t v___x_2405_; 
lean_inc(v___x_2403_);
v___x_2405_ = l_Lean_Syntax_matchesNull(v___x_2403_, v___x_2276_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; 
lean_dec(v___x_2403_);
lean_dec(v___x_2277_);
v___x_2406_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2406_;
}
else
{
lean_object* v___x_2407_; lean_object* v_types_2408_; lean_object* v___x_2409_; uint8_t v___x_2410_; 
v___x_2407_ = lean_unsigned_to_nat(0u);
v_types_2408_ = l_Lean_Syntax_getArg(v___x_2403_, v___x_2407_);
lean_dec(v___x_2403_);
v___x_2409_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__7));
lean_inc(v_types_2408_);
v___x_2410_ = l_Lean_Syntax_isOfKind(v_types_2408_, v___x_2409_);
if (v___x_2410_ == 0)
{
lean_object* v___x_2411_; 
lean_dec(v_types_2408_);
lean_dec(v___x_2277_);
v___x_2411_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
return v___x_2411_;
}
else
{
lean_object* v___x_2412_; 
v___x_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2412_, 0, v_types_2408_);
v_types_2281_ = v___x_2412_;
v___y_2282_ = v_a_2264_;
v___y_2283_ = v_a_2265_;
v___y_2284_ = v_a_2266_;
v___y_2285_ = v_a_2267_;
v___y_2286_ = v_a_2268_;
v___y_2287_ = v_a_2269_;
v___y_2288_ = v_a_2270_;
v___y_2289_ = v_a_2271_;
goto v___jp_2280_;
}
}
}
else
{
lean_object* v___x_2413_; 
lean_dec(v___x_2403_);
v___x_2413_ = lean_box(0);
v_types_2281_ = v___x_2413_;
v___y_2282_ = v_a_2264_;
v___y_2283_ = v_a_2265_;
v___y_2284_ = v_a_2266_;
v___y_2285_ = v_a_2267_;
v___y_2286_ = v_a_2268_;
v___y_2287_ = v_a_2269_;
v___y_2288_ = v_a_2270_;
v___y_2289_ = v_a_2271_;
goto v___jp_2280_;
}
}
v___jp_2280_:
{
lean_object* v___x_2290_; 
v___x_2290_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_2288_, v___y_2289_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2399_; 
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2399_ == 0)
{
lean_object* v_unused_2400_; 
v_unused_2400_ = lean_ctor_get(v___x_2290_, 0);
lean_dec(v_unused_2400_);
v___x_2292_ = v___x_2290_;
v_isShared_2293_ = v_isSharedCheck_2399_;
goto v_resetjp_2291_;
}
else
{
lean_dec(v___x_2290_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2399_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2294_; uint8_t v___x_2295_; lean_object* v___x_2296_; uint8_t v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2294_ = lean_unsigned_to_nat(10u);
v___x_2295_ = 0;
v___x_2296_ = lean_unsigned_to_nat(100000u);
v___x_2297_ = 0;
v___x_2298_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_2298_, 0, v___x_2294_);
lean_ctor_set(v___x_2298_, 1, v___x_2296_);
lean_ctor_set_uint8(v___x_2298_, sizeof(void*)*2, v___x_2279_);
lean_ctor_set_uint8(v___x_2298_, sizeof(void*)*2 + 1, v___x_2279_);
lean_ctor_set_uint8(v___x_2298_, sizeof(void*)*2 + 2, v___x_2295_);
lean_ctor_set_uint8(v___x_2298_, sizeof(void*)*2 + 3, v___x_2279_);
lean_ctor_set_uint8(v___x_2298_, sizeof(void*)*2 + 4, v___x_2279_);
lean_ctor_set_uint8(v___x_2298_, sizeof(void*)*2 + 5, v___x_2279_);
lean_ctor_set_uint8(v___x_2298_, sizeof(void*)*2 + 6, v___x_2279_);
lean_ctor_set_uint8(v___x_2298_, sizeof(void*)*2 + 7, v___x_2279_);
lean_ctor_set_uint8(v___x_2298_, sizeof(void*)*2 + 8, v___x_2295_);
lean_ctor_set_uint8(v___x_2298_, sizeof(void*)*2 + 9, v___x_2295_);
lean_ctor_set_uint8(v___x_2298_, sizeof(void*)*2 + 10, v___x_2297_);
v___x_2299_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_2277_, v___x_2298_, v___x_2279_, v___y_2282_, v___y_2288_, v___y_2289_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2301_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v___x_2301_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_types_2281_, v_a_2300_, v___y_2288_, v___y_2289_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2303_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2302_);
lean_dec_ref_known(v___x_2301_, 1);
v___x_2303_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2283_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2303_, 1);
v___x_2305_ = lean_unsigned_to_nat(9u);
v___x_2306_ = lean_unsigned_to_nat(5u);
v___x_2307_ = lean_unsigned_to_nat(8u);
v___x_2308_ = lean_unsigned_to_nat(1000u);
v___x_2309_ = lean_unsigned_to_nat(1024u);
v___x_2310_ = lean_unsigned_to_nat(10000u);
v___x_2311_ = lean_unsigned_to_nat(1048576u);
v___x_2312_ = lean_unsigned_to_nat(50u);
v___x_2313_ = lean_box(0);
v___x_2314_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_2314_, 0, v___x_2305_);
lean_ctor_set(v___x_2314_, 1, v___x_2306_);
lean_ctor_set(v___x_2314_, 2, v___x_2307_);
lean_ctor_set(v___x_2314_, 3, v___x_2307_);
lean_ctor_set(v___x_2314_, 4, v___x_2308_);
lean_ctor_set(v___x_2314_, 5, v___x_2308_);
lean_ctor_set(v___x_2314_, 6, v___x_2296_);
lean_ctor_set(v___x_2314_, 7, v___x_2309_);
lean_ctor_set(v___x_2314_, 8, v___x_2310_);
lean_ctor_set(v___x_2314_, 9, v___x_2308_);
lean_ctor_set(v___x_2314_, 10, v___x_2311_);
lean_ctor_set(v___x_2314_, 11, v___x_2294_);
lean_ctor_set(v___x_2314_, 12, v___x_2312_);
lean_ctor_set(v___x_2314_, 13, v___x_2313_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14, v___x_2295_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 1, v___x_2295_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 2, v___x_2295_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 3, v___x_2295_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 4, v___x_2295_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 5, v___x_2279_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 6, v___x_2279_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 7, v___x_2279_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 8, v___x_2295_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 9, v___x_2295_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 10, v___x_2279_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 11, v___x_2295_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 12, v___x_2279_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 13, v___x_2279_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 14, v___x_2279_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 15, v___x_2279_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 16, v___x_2279_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 17, v___x_2295_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 18, v___x_2279_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 19, v___x_2279_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 20, v___x_2279_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 21, v___x_2279_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 22, v___x_2279_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 23, v___x_2279_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 24, v___x_2279_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 25, v___x_2279_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 26, v___x_2279_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 27, v___x_2279_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 28, v___x_2279_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 29, v___x_2279_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 30, v___x_2295_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 31, v___x_2279_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*14 + 32, v___x_2279_);
v___x_2315_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_2314_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2318_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 0, v_a_2302_);
v___x_2318_ = v___x_2292_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2302_);
v___x_2318_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___f_2322_; lean_object* v___x_2323_; 
v___x_2319_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v___x_2318_, v_a_2300_);
v___x_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2320_, 0, v_a_2304_);
v___x_2321_ = lean_box(v___x_2295_);
v___f_2322_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___lam__0___boxed), 13, 3);
lean_closure_set(v___f_2322_, 0, v___x_2320_);
lean_closure_set(v___f_2322_, 1, v___x_2321_);
lean_closure_set(v___f_2322_, 2, v___x_2319_);
v___x_2323_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___f_2322_, v_a_2316_, v___x_2313_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v_snd_2325_; lean_object* v_target_2326_; lean_object* v_hypotheses_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v_a_2330_; uint8_t v___x_2331_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2323_, 1);
v_snd_2325_ = lean_ctor_get(v_a_2324_, 1);
lean_inc(v_snd_2325_);
lean_dec(v_a_2324_);
v_target_2326_ = lean_ctor_get(v_snd_2325_, 2);
lean_inc_ref(v_target_2326_);
v_hypotheses_2327_ = lean_ctor_get(v_snd_2325_, 3);
lean_inc_ref(v_hypotheses_2327_);
lean_dec(v_snd_2325_);
v___x_2328_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_2326_);
lean_dec_ref(v_target_2326_);
v___x_2329_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(v___x_2328_, v___y_2287_);
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref(v___x_2329_);
v___x_2331_ = lean_unbox(v_a_2330_);
lean_dec(v_a_2330_);
if (v___x_2331_ == 0)
{
size_t v_sz_2332_; size_t v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v_sz_2332_ = lean_array_size(v_hypotheses_2327_);
v___x_2333_ = ((size_t)0ULL);
v___x_2334_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__1(v_sz_2332_, v___x_2333_, v_hypotheses_2327_);
v___x_2335_ = l_Lean_MVarId_assertHypotheses(v___x_2328_, v___x_2334_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v_snd_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2346_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref_known(v___x_2335_, 1);
v_snd_2337_ = lean_ctor_get(v_a_2336_, 1);
v_isSharedCheck_2346_ = !lean_is_exclusive(v_a_2336_);
if (v_isSharedCheck_2346_ == 0)
{
lean_object* v_unused_2347_; 
v_unused_2347_ = lean_ctor_get(v_a_2336_, 0);
lean_dec(v_unused_2347_);
v___x_2339_ = v_a_2336_;
v_isShared_2340_ = v_isSharedCheck_2346_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_snd_2337_);
lean_dec(v_a_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2346_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2341_; lean_object* v___x_2343_; 
v___x_2341_ = lean_box(0);
if (v_isShared_2340_ == 0)
{
lean_ctor_set_tag(v___x_2339_, 1);
lean_ctor_set(v___x_2339_, 1, v___x_2341_);
lean_ctor_set(v___x_2339_, 0, v_snd_2337_);
v___x_2343_ = v___x_2339_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_snd_2337_);
lean_ctor_set(v_reuseFailAlloc_2345_, 1, v___x_2341_);
v___x_2343_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
lean_object* v___x_2344_; 
v___x_2344_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2343_, v___y_2283_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
return v___x_2344_;
}
}
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
v_a_2348_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2335_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2335_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2351_ == 0)
{
v___x_2353_ = v___x_2350_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2348_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
else
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
lean_dec(v___x_2328_);
lean_dec_ref(v_hypotheses_2327_);
v___x_2356_ = lean_box(0);
v___x_2357_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2356_, v___y_2283_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
return v___x_2357_;
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
v_a_2358_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2323_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2323_);
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
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
lean_dec(v_a_2304_);
lean_dec(v_a_2302_);
lean_dec(v_a_2300_);
lean_del_object(v___x_2292_);
v_a_2367_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2315_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2315_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
lean_dec(v_a_2302_);
lean_dec(v_a_2300_);
lean_del_object(v___x_2292_);
v_a_2375_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2303_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2303_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
lean_dec(v_a_2300_);
lean_del_object(v___x_2292_);
v_a_2383_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2385_ = v___x_2301_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2301_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2383_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
lean_del_object(v___x_2292_);
lean_dec(v_types_2281_);
v_a_2391_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2299_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2299_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
}
else
{
lean_dec(v_types_2281_);
lean_dec(v___x_2277_);
return v___x_2290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___boxed(lean_object* v_x_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Lean_Elab_Tactic_BVDecide_evalBVNormalize(v_x_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
lean_dec(v_a_2422_);
lean_dec_ref(v_a_2421_);
lean_dec(v_a_2420_);
lean_dec_ref(v_a_2419_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0(lean_object* v_mvarId_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___redArg(v_mvarId_2425_, v___y_2431_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0___boxed(lean_object* v_mvarId_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0(v_mvarId_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v_mvarId_2436_);
return v_res_2446_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0(lean_object* v_00_u03b2_2447_, lean_object* v_x_2448_, lean_object* v_x_2449_){
_start:
{
uint8_t v___x_2450_; 
v___x_2450_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___redArg(v_x_2448_, v_x_2449_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2451_, lean_object* v_x_2452_, lean_object* v_x_2453_){
_start:
{
uint8_t v_res_2454_; lean_object* v_r_2455_; 
v_res_2454_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0(v_00_u03b2_2451_, v_x_2452_, v_x_2453_);
lean_dec(v_x_2453_);
lean_dec_ref(v_x_2452_);
v_r_2455_ = lean_box(v_res_2454_);
return v_r_2455_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2456_, lean_object* v_x_2457_, size_t v_x_2458_, lean_object* v_x_2459_){
_start:
{
uint8_t v___x_2460_; 
v___x_2460_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_2457_, v_x_2458_, v_x_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2461_, lean_object* v_x_2462_, lean_object* v_x_2463_, lean_object* v_x_2464_){
_start:
{
size_t v_x_5145__boxed_2465_; uint8_t v_res_2466_; lean_object* v_r_2467_; 
v_x_5145__boxed_2465_ = lean_unbox_usize(v_x_2463_);
lean_dec(v_x_2463_);
v_res_2466_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1(v_00_u03b2_2461_, v_x_2462_, v_x_5145__boxed_2465_, v_x_2464_);
lean_dec(v_x_2464_);
lean_dec_ref(v_x_2462_);
v_r_2467_ = lean_box(v_res_2466_);
return v_r_2467_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2468_, lean_object* v_keys_2469_, lean_object* v_vals_2470_, lean_object* v_heq_2471_, lean_object* v_i_2472_, lean_object* v_k_2473_){
_start:
{
uint8_t v___x_2474_; 
v___x_2474_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2469_, v_i_2472_, v_k_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2475_, lean_object* v_keys_2476_, lean_object* v_vals_2477_, lean_object* v_heq_2478_, lean_object* v_i_2479_, lean_object* v_k_2480_){
_start:
{
uint8_t v_res_2481_; lean_object* v_r_2482_; 
v_res_2481_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_BVDecide_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2475_, v_keys_2476_, v_vals_2477_, v_heq_2478_, v_i_2479_, v_k_2480_);
lean_dec(v_k_2480_);
lean_dec_ref(v_vals_2477_);
lean_dec_ref(v_keys_2476_);
v_r_2482_ = lean_box(v_res_2481_);
return v_r_2482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1(){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2491_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2492_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___closed__0));
v___x_2493_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___closed__1));
v___x_2494_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_evalBVNormalize___boxed), 10, 0);
v___x_2495_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2491_, v___x_2492_, v___x_2493_, v___x_2494_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1___boxed(lean_object* v_a_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l___private_Lean_Elab_Tactic_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBVNormalize___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBVNormalize__1();
return v_res_2497_;
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
