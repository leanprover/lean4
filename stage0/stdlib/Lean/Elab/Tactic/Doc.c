// Lean compiler output
// Module: Lean.Elab.Tactic.Doc
// Imports: import Lean.DocString public import Lean.Elab.Command public import Lean.Parser.Tactic.Doc
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
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
lean_object* l_Lean_TSyntax_getDocString(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Parser_Tactic_Doc_isTactic(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_Doc_alternativeOfTactic(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_withExprHover(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_tacticNameExt;
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_constants(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_tacticTagExt;
extern lean_object* l_Lean_Parser_parserExtension;
extern lean_object* l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_nestD(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensions(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "tactic_extension"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_value),LEAN_SCALAR_PTR_LITERAL(226, 244, 145, 122, 23, 135, 199, 68)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Malformed tactic extension command"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "` is not a tactic"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "` is an alternative form of `"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Missing documentation comment"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__17_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "elabTacticExtension"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(128, 44, 144, 107, 80, 40, 109, 178)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value),((lean_object*)(((size_t)(43) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected doc string"};
static const lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0 = (const lean_object*)&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1;
static const lean_string_object l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "versoCommentBody"};
static const lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2 = (const lean_object*)&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Malformed 'register_tactic_tag' command"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "register_tactic_tag"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value),LEAN_SCALAR_PTR_LITERAL(207, 55, 57, 11, 65, 76, 175, 2)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "elabRegisterTacticTag"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 30, 89, 153, 147, 186, 30, 23)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(46) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value),((lean_object*)(((size_t)(46) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 68, 185, 128, 48, 210, 24, 186)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0_value)} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2;
static const lean_closure_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_param___override, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32_spec__36___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32_spec__36___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0_value;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "• "};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 4, .m_data = " — \""};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7_value;
static const lean_ctor_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7_value)}};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0;
static const lean_array_object l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Available tags: "};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32_spec__36(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32_spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "printTacTags"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 6, 105, 20, 120, 144, 238, 207)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "elabPrintTacTags"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(202, 38, 126, 200, 28, 172, 117, 128)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "Displays all available tactic tags, with documentation.\n"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(37) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(130) << 1) | 1)),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value),((lean_object*)(((size_t)(37) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value),((lean_object*)(((size_t)(41) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(lean_object* v___x_1_, lean_object* v___x_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_1_, v___x_2_, v___y_7_, v___y_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed(lean_object* v___x_11_, lean_object* v___x_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(v___x_11_, v___x_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_20_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_21_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0);
v___x_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
return v___x_23_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1);
v___x_25_ = lean_unsigned_to_nat(0u);
v___x_26_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
lean_ctor_set(v___x_26_, 2, v___x_25_);
lean_ctor_set(v___x_26_, 3, v___x_25_);
lean_ctor_set(v___x_26_, 4, v___x_24_);
lean_ctor_set(v___x_26_, 5, v___x_24_);
lean_ctor_set(v___x_26_, 6, v___x_24_);
lean_ctor_set(v___x_26_, 7, v___x_24_);
lean_ctor_set(v___x_26_, 8, v___x_24_);
lean_ctor_set(v___x_26_, 9, v___x_24_);
lean_ctor_set(v___x_26_, 10, v___x_24_);
return v___x_26_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_unsigned_to_nat(32u);
v___x_28_ = lean_mk_empty_array_with_capacity(v___x_27_);
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4(void){
_start:
{
size_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_30_ = ((size_t)5ULL);
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_unsigned_to_nat(32u);
v___x_33_ = lean_mk_empty_array_with_capacity(v___x_32_);
v___x_34_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3);
v___x_35_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_35_, 0, v___x_34_);
lean_ctor_set(v___x_35_, 1, v___x_33_);
lean_ctor_set(v___x_35_, 2, v___x_31_);
lean_ctor_set(v___x_35_, 3, v___x_31_);
lean_ctor_set_usize(v___x_35_, 4, v___x_30_);
return v___x_35_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_36_ = lean_box(1);
v___x_37_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4);
v___x_38_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1);
v___x_39_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
lean_ctor_set(v___x_39_, 1, v___x_37_);
lean_ctor_set(v___x_39_, 2, v___x_36_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(lean_object* v_msgData_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___x_43_; lean_object* v_env_44_; lean_object* v___x_45_; lean_object* v_scopes_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v_opts_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_43_ = lean_st_ref_get(v___y_41_);
v_env_44_ = lean_ctor_get(v___x_43_, 0);
lean_inc_ref(v_env_44_);
lean_dec(v___x_43_);
v___x_45_ = lean_st_ref_get(v___y_41_);
v_scopes_46_ = lean_ctor_get(v___x_45_, 2);
lean_inc(v_scopes_46_);
lean_dec(v___x_45_);
v___x_47_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_48_ = l_List_head_x21___redArg(v___x_47_, v_scopes_46_);
lean_dec(v_scopes_46_);
v_opts_49_ = lean_ctor_get(v___x_48_, 1);
lean_inc_ref(v_opts_49_);
lean_dec(v___x_48_);
v___x_50_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2);
v___x_51_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5);
v___x_52_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_52_, 0, v_env_44_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
lean_ctor_set(v___x_52_, 2, v___x_51_);
lean_ctor_set(v___x_52_, 3, v_opts_49_);
v___x_53_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v_msgData_40_);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___boxed(lean_object* v_msgData_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msgData_55_, v___y_56_);
lean_dec(v___y_56_);
return v_res_58_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_box(1);
v___x_60_ = l_Lean_MessageData_ofFormat(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__2));
v___x_65_ = l_Lean_MessageData_ofFormat(v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3(lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
if (lean_obj_tag(v_x_67_) == 0)
{
return v_x_66_;
}
else
{
lean_object* v_head_68_; lean_object* v_tail_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_91_; 
v_head_68_ = lean_ctor_get(v_x_67_, 0);
v_tail_69_ = lean_ctor_get(v_x_67_, 1);
v_isSharedCheck_91_ = !lean_is_exclusive(v_x_67_);
if (v_isSharedCheck_91_ == 0)
{
v___x_71_ = v_x_67_;
v_isShared_72_ = v_isSharedCheck_91_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_tail_69_);
lean_inc(v_head_68_);
lean_dec(v_x_67_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_91_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v_before_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_89_; 
v_before_73_ = lean_ctor_get(v_head_68_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v_head_68_);
if (v_isSharedCheck_89_ == 0)
{
lean_object* v_unused_90_; 
v_unused_90_ = lean_ctor_get(v_head_68_, 1);
lean_dec(v_unused_90_);
v___x_75_ = v_head_68_;
v_isShared_76_ = v_isSharedCheck_89_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_before_73_);
lean_dec(v_head_68_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_89_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; lean_object* v___x_79_; 
v___x_77_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_76_ == 0)
{
lean_ctor_set_tag(v___x_75_, 7);
lean_ctor_set(v___x_75_, 1, v___x_77_);
lean_ctor_set(v___x_75_, 0, v_x_66_);
v___x_79_ = v___x_75_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_x_66_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v___x_77_);
v___x_79_ = v_reuseFailAlloc_88_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_80_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_72_ == 0)
{
lean_ctor_set_tag(v___x_71_, 7);
lean_ctor_set(v___x_71_, 1, v___x_80_);
lean_ctor_set(v___x_71_, 0, v___x_79_);
v___x_82_ = v___x_71_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_79_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v___x_80_);
v___x_82_ = v_reuseFailAlloc_87_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = l_Lean_MessageData_ofSyntax(v_before_73_);
v___x_84_ = l_Lean_indentD(v___x_83_);
v___x_85_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_82_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v_x_66_ = v___x_85_;
v_x_67_ = v_tail_69_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(lean_object* v_opts_92_, lean_object* v_opt_93_){
_start:
{
lean_object* v_name_94_; lean_object* v_defValue_95_; lean_object* v_map_96_; lean_object* v___x_97_; 
v_name_94_ = lean_ctor_get(v_opt_93_, 0);
v_defValue_95_ = lean_ctor_get(v_opt_93_, 1);
v_map_96_ = lean_ctor_get(v_opts_92_, 0);
v___x_97_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_96_, v_name_94_);
if (lean_obj_tag(v___x_97_) == 0)
{
uint8_t v___x_98_; 
v___x_98_ = lean_unbox(v_defValue_95_);
return v___x_98_;
}
else
{
lean_object* v_val_99_; 
v_val_99_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_val_99_);
lean_dec_ref_known(v___x_97_, 1);
if (lean_obj_tag(v_val_99_) == 1)
{
uint8_t v_v_100_; 
v_v_100_ = lean_ctor_get_uint8(v_val_99_, 0);
lean_dec_ref_known(v_val_99_, 0);
return v_v_100_;
}
else
{
uint8_t v___x_101_; 
lean_dec(v_val_99_);
v___x_101_ = lean_unbox(v_defValue_95_);
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_102_, lean_object* v_opt_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_102_, v_opt_103_);
lean_dec_ref(v_opt_103_);
lean_dec_ref(v_opts_102_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__1));
v___x_110_ = l_Lean_MessageData_ofFormat(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(lean_object* v_msgData_111_, lean_object* v_macroStack_112_, lean_object* v___y_113_){
_start:
{
lean_object* v___x_115_; lean_object* v_scopes_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v_opts_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_115_ = lean_st_ref_get(v___y_113_);
v_scopes_116_ = lean_ctor_get(v___x_115_, 2);
lean_inc(v_scopes_116_);
lean_dec(v___x_115_);
v___x_117_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_118_ = l_List_head_x21___redArg(v___x_117_, v_scopes_116_);
lean_dec(v_scopes_116_);
v_opts_119_ = lean_ctor_get(v___x_118_, 1);
lean_inc_ref(v_opts_119_);
lean_dec(v___x_118_);
v___x_120_ = l_Lean_Elab_pp_macroStack;
v___x_121_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_119_, v___x_120_);
lean_dec_ref(v_opts_119_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; 
lean_dec(v_macroStack_112_);
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v_msgData_111_);
return v___x_122_;
}
else
{
if (lean_obj_tag(v_macroStack_112_) == 0)
{
lean_object* v___x_123_; 
v___x_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_123_, 0, v_msgData_111_);
return v___x_123_;
}
else
{
lean_object* v_head_124_; lean_object* v_after_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_140_; 
v_head_124_ = lean_ctor_get(v_macroStack_112_, 0);
lean_inc(v_head_124_);
v_after_125_ = lean_ctor_get(v_head_124_, 1);
v_isSharedCheck_140_ = !lean_is_exclusive(v_head_124_);
if (v_isSharedCheck_140_ == 0)
{
lean_object* v_unused_141_; 
v_unused_141_ = lean_ctor_get(v_head_124_, 0);
lean_dec(v_unused_141_);
v___x_127_ = v_head_124_;
v_isShared_128_ = v_isSharedCheck_140_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_after_125_);
lean_dec(v_head_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_140_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_129_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_128_ == 0)
{
lean_ctor_set_tag(v___x_127_, 7);
lean_ctor_set(v___x_127_, 1, v___x_129_);
lean_ctor_set(v___x_127_, 0, v_msgData_111_);
v___x_131_ = v___x_127_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_msgData_111_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v___x_129_);
v___x_131_ = v_reuseFailAlloc_139_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v_msgData_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_132_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2);
v___x_133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_131_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = l_Lean_MessageData_ofSyntax(v_after_125_);
v___x_135_ = l_Lean_indentD(v___x_134_);
v_msgData_136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_136_, 0, v___x_133_);
lean_ctor_set(v_msgData_136_, 1, v___x_135_);
v___x_137_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3(v_msgData_136_, v_macroStack_112_);
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
return v___x_138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_142_, lean_object* v_macroStack_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(v_msgData_142_, v_macroStack_143_, v___y_144_);
lean_dec(v___y_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(lean_object* v_msg_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Elab_Command_getRef___redArg(v___y_148_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; lean_object* v_macroStack_153_; lean_object* v___x_154_; lean_object* v_a_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_166_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_a_152_);
lean_dec_ref_known(v___x_151_, 1);
v_macroStack_153_ = lean_ctor_get(v___y_148_, 4);
v___x_154_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msg_147_, v___y_149_);
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref(v___x_154_);
v___x_156_ = l_Lean_Elab_getBetterRef(v_a_152_, v_macroStack_153_);
lean_dec(v_a_152_);
lean_inc(v_macroStack_153_);
v___x_157_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(v_a_155_, v_macroStack_153_, v___y_149_);
v_a_158_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_166_ == 0)
{
v___x_160_ = v___x_157_;
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_157_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_156_);
lean_ctor_set(v___x_162_, 1, v_a_158_);
if (v_isShared_161_ == 0)
{
lean_ctor_set_tag(v___x_160_, 1);
lean_ctor_set(v___x_160_, 0, v___x_162_);
v___x_164_ = v___x_160_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
else
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
lean_dec_ref(v_msg_147_);
v_a_167_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v___x_151_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_151_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg___boxed(lean_object* v_msg_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v_msg_175_, v___y_176_, v___y_177_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(lean_object* v_ref_180_, lean_object* v_msg_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_Elab_Command_getRef___redArg(v___y_182_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v_fileName_187_; lean_object* v_fileMap_188_; lean_object* v_currRecDepth_189_; lean_object* v_cmdPos_190_; lean_object* v_macroStack_191_; lean_object* v_quotContext_x3f_192_; lean_object* v_currMacroScope_193_; lean_object* v_snap_x3f_194_; lean_object* v_cancelTk_x3f_195_; uint8_t v_suppressElabErrors_196_; lean_object* v_ref_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_186_);
lean_dec_ref_known(v___x_185_, 1);
v_fileName_187_ = lean_ctor_get(v___y_182_, 0);
v_fileMap_188_ = lean_ctor_get(v___y_182_, 1);
v_currRecDepth_189_ = lean_ctor_get(v___y_182_, 2);
v_cmdPos_190_ = lean_ctor_get(v___y_182_, 3);
v_macroStack_191_ = lean_ctor_get(v___y_182_, 4);
v_quotContext_x3f_192_ = lean_ctor_get(v___y_182_, 5);
v_currMacroScope_193_ = lean_ctor_get(v___y_182_, 6);
v_snap_x3f_194_ = lean_ctor_get(v___y_182_, 8);
v_cancelTk_x3f_195_ = lean_ctor_get(v___y_182_, 9);
v_suppressElabErrors_196_ = lean_ctor_get_uint8(v___y_182_, sizeof(void*)*10);
v_ref_197_ = l_Lean_replaceRef(v_ref_180_, v_a_186_);
lean_dec(v_a_186_);
lean_inc(v_cancelTk_x3f_195_);
lean_inc(v_snap_x3f_194_);
lean_inc(v_currMacroScope_193_);
lean_inc(v_quotContext_x3f_192_);
lean_inc(v_macroStack_191_);
lean_inc(v_cmdPos_190_);
lean_inc(v_currRecDepth_189_);
lean_inc_ref(v_fileMap_188_);
lean_inc_ref(v_fileName_187_);
v___x_198_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_198_, 0, v_fileName_187_);
lean_ctor_set(v___x_198_, 1, v_fileMap_188_);
lean_ctor_set(v___x_198_, 2, v_currRecDepth_189_);
lean_ctor_set(v___x_198_, 3, v_cmdPos_190_);
lean_ctor_set(v___x_198_, 4, v_macroStack_191_);
lean_ctor_set(v___x_198_, 5, v_quotContext_x3f_192_);
lean_ctor_set(v___x_198_, 6, v_currMacroScope_193_);
lean_ctor_set(v___x_198_, 7, v_ref_197_);
lean_ctor_set(v___x_198_, 8, v_snap_x3f_194_);
lean_ctor_set(v___x_198_, 9, v_cancelTk_x3f_195_);
lean_ctor_set_uint8(v___x_198_, sizeof(void*)*10, v_suppressElabErrors_196_);
v___x_199_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v_msg_181_, v___x_198_, v___y_183_);
lean_dec_ref_known(v___x_198_, 10);
return v___x_199_;
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec_ref(v_msg_181_);
v_a_200_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_185_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_185_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg___boxed(lean_object* v_ref_208_, lean_object* v_msg_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_ref_208_, v_msg_209_, v___y_210_, v___y_211_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v_ref_208_);
return v_res_213_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5));
v___x_225_ = l_Lean_stringToMessageData(v___x_224_);
return v___x_225_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11));
v___x_237_ = l_Lean_stringToMessageData(v___x_236_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13));
v___x_240_ = l_Lean_stringToMessageData(v___x_239_);
return v___x_240_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15));
v___x_243_ = l_Lean_stringToMessageData(v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__17));
v___x_246_ = l_Lean_stringToMessageData(v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension(lean_object* v_x_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4));
lean_inc(v_x_247_);
v___x_252_ = l_Lean_Syntax_isOfKind(v_x_247_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec(v_x_247_);
v___x_253_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_254_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_253_, v_a_248_, v_a_249_);
return v___x_254_;
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_255_ = lean_unsigned_to_nat(0u);
v___x_256_ = l_Lean_Syntax_getArg(v_x_247_, v___x_255_);
lean_inc(v___x_256_);
v___x_257_ = l_Lean_Syntax_matchesNull(v___x_256_, v___x_255_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_256_);
v___x_259_ = l_Lean_Syntax_matchesNull(v___x_256_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec(v___x_256_);
lean_dec(v_x_247_);
v___x_260_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_261_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_260_, v_a_248_, v_a_249_);
return v___x_261_;
}
else
{
lean_object* v_docs_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_docs_262_ = l_Lean_Syntax_getArg(v___x_256_, v___x_255_);
lean_dec(v___x_256_);
v___x_263_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8));
lean_inc(v_docs_262_);
v___x_264_ = l_Lean_Syntax_isOfKind(v_docs_262_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec(v_docs_262_);
lean_dec(v_x_247_);
v___x_265_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_266_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_265_, v_a_248_, v_a_249_);
return v___x_266_;
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_267_ = lean_unsigned_to_nat(2u);
v___x_268_ = l_Lean_Syntax_getArg(v_x_247_, v___x_267_);
lean_dec(v_x_247_);
v___x_269_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10));
lean_inc(v___x_268_);
v___x_270_ = l_Lean_Syntax_isOfKind(v___x_268_, v___x_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec(v___x_268_);
lean_dec(v_docs_262_);
v___x_271_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_272_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_271_, v_a_248_, v_a_249_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; lean_object* v___f_274_; lean_object* v___x_275_; 
v___x_273_ = lean_box(0);
lean_inc(v___x_268_);
v___f_274_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed), 9, 2);
lean_closure_set(v___f_274_, 0, v___x_268_);
lean_closure_set(v___f_274_, 1, v___x_273_);
v___x_275_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_274_, v_a_248_, v_a_249_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_343_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_343_ == 0)
{
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_343_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_343_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___y_281_; lean_object* v___y_315_; lean_object* v___y_316_; uint8_t v___y_317_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___x_330_; lean_object* v_env_331_; lean_object* v___x_332_; 
v___x_330_ = lean_st_ref_get(v_a_249_);
v_env_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc_ref(v_env_331_);
lean_dec(v___x_330_);
lean_inc(v_a_276_);
v___x_332_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_331_, v_a_276_);
if (lean_obj_tag(v___x_332_) == 1)
{
lean_object* v_val_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
lean_del_object(v___x_278_);
lean_dec(v_docs_262_);
v_val_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_val_333_);
lean_dec_ref_known(v___x_332_, 1);
v___x_334_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_335_ = l_Lean_MessageData_ofConstName(v_a_276_, v___x_257_);
v___x_336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_334_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16);
v___x_338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_336_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = l_Lean_MessageData_ofConstName(v_val_333_, v___x_257_);
v___x_340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_338_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v___x_334_);
v___x_342_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v___x_268_, v___x_341_, v_a_248_, v_a_249_);
lean_dec(v___x_268_);
return v___x_342_;
}
else
{
lean_dec(v___x_332_);
v___y_325_ = v_a_248_;
v___y_326_ = v_a_249_;
goto v___jp_324_;
}
v___jp_280_:
{
lean_object* v___x_282_; lean_object* v_env_283_; lean_object* v_messages_284_; lean_object* v_scopes_285_; lean_object* v_usedQuotCtxts_286_; lean_object* v_nextMacroScope_287_; lean_object* v_maxRecDepth_288_; lean_object* v_ngen_289_; lean_object* v_auxDeclNGen_290_; lean_object* v_infoState_291_; lean_object* v_traceState_292_; lean_object* v_snapshotTasks_293_; lean_object* v_prevLinterStates_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_313_; 
v___x_282_ = lean_st_ref_take(v___y_281_);
v_env_283_ = lean_ctor_get(v___x_282_, 0);
v_messages_284_ = lean_ctor_get(v___x_282_, 1);
v_scopes_285_ = lean_ctor_get(v___x_282_, 2);
v_usedQuotCtxts_286_ = lean_ctor_get(v___x_282_, 3);
v_nextMacroScope_287_ = lean_ctor_get(v___x_282_, 4);
v_maxRecDepth_288_ = lean_ctor_get(v___x_282_, 5);
v_ngen_289_ = lean_ctor_get(v___x_282_, 6);
v_auxDeclNGen_290_ = lean_ctor_get(v___x_282_, 7);
v_infoState_291_ = lean_ctor_get(v___x_282_, 8);
v_traceState_292_ = lean_ctor_get(v___x_282_, 9);
v_snapshotTasks_293_ = lean_ctor_get(v___x_282_, 10);
v_prevLinterStates_294_ = lean_ctor_get(v___x_282_, 11);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_313_ == 0)
{
v___x_296_ = v___x_282_;
v_isShared_297_ = v_isSharedCheck_313_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_prevLinterStates_294_);
lean_inc(v_snapshotTasks_293_);
lean_inc(v_traceState_292_);
lean_inc(v_infoState_291_);
lean_inc(v_auxDeclNGen_290_);
lean_inc(v_ngen_289_);
lean_inc(v_maxRecDepth_288_);
lean_inc(v_nextMacroScope_287_);
lean_inc(v_usedQuotCtxts_286_);
lean_inc(v_scopes_285_);
lean_inc(v_messages_284_);
lean_inc(v_env_283_);
lean_dec(v___x_282_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_313_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v_toEnvExtension_299_; lean_object* v_asyncMode_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_306_; 
v___x_298_ = l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
v_toEnvExtension_299_ = lean_ctor_get(v___x_298_, 0);
v_asyncMode_300_ = lean_ctor_get(v_toEnvExtension_299_, 2);
v___x_301_ = l_Lean_TSyntax_getDocString(v_docs_262_);
lean_dec(v_docs_262_);
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v_a_276_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = lean_box(0);
v___x_304_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_298_, v_env_283_, v___x_302_, v_asyncMode_300_, v___x_303_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_304_);
v___x_306_ = v___x_296_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_messages_284_);
lean_ctor_set(v_reuseFailAlloc_312_, 2, v_scopes_285_);
lean_ctor_set(v_reuseFailAlloc_312_, 3, v_usedQuotCtxts_286_);
lean_ctor_set(v_reuseFailAlloc_312_, 4, v_nextMacroScope_287_);
lean_ctor_set(v_reuseFailAlloc_312_, 5, v_maxRecDepth_288_);
lean_ctor_set(v_reuseFailAlloc_312_, 6, v_ngen_289_);
lean_ctor_set(v_reuseFailAlloc_312_, 7, v_auxDeclNGen_290_);
lean_ctor_set(v_reuseFailAlloc_312_, 8, v_infoState_291_);
lean_ctor_set(v_reuseFailAlloc_312_, 9, v_traceState_292_);
lean_ctor_set(v_reuseFailAlloc_312_, 10, v_snapshotTasks_293_);
lean_ctor_set(v_reuseFailAlloc_312_, 11, v_prevLinterStates_294_);
v___x_306_ = v_reuseFailAlloc_312_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v___x_307_ = lean_st_ref_put(v___y_281_, v___x_306_);
v___x_308_ = lean_box(0);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v___x_308_);
v___x_310_ = v___x_278_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
v___jp_314_:
{
if (v___y_317_ == 0)
{
lean_dec(v___x_268_);
v___y_281_ = v___y_315_;
goto v___jp_280_;
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
lean_del_object(v___x_278_);
lean_dec(v_docs_262_);
v___x_318_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_319_ = l_Lean_MessageData_ofConstName(v_a_276_, v___x_257_);
v___x_320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14);
v___x_322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_320_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
v___x_323_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v___x_268_, v___x_322_, v___y_316_, v___y_315_);
lean_dec(v___x_268_);
return v___x_323_;
}
}
v___jp_324_:
{
lean_object* v___x_327_; lean_object* v_env_328_; uint8_t v___x_329_; 
v___x_327_ = lean_st_ref_get(v___y_326_);
v_env_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc_ref(v_env_328_);
lean_dec(v___x_327_);
v___x_329_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_328_, v_a_276_);
if (v___x_329_ == 0)
{
v___y_315_ = v___y_326_;
v___y_316_ = v___y_325_;
v___y_317_ = v___x_270_;
goto v___jp_314_;
}
else
{
v___y_315_ = v___y_326_;
v___y_316_ = v___y_325_;
v___y_317_ = v___x_257_;
goto v___jp_314_;
}
}
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec(v___x_268_);
lean_dec(v_docs_262_);
v_a_344_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_275_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_275_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_352_; lean_object* v_cmd_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec(v___x_256_);
v___x_352_ = lean_unsigned_to_nat(1u);
v_cmd_353_ = l_Lean_Syntax_getArg(v_x_247_, v___x_352_);
lean_dec(v_x_247_);
v___x_354_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18);
v___x_355_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_cmd_353_, v___x_354_, v_a_248_, v_a_249_);
lean_dec(v_cmd_353_);
return v___x_355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed(lean_object* v_x_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension(v_x_356_, v_a_357_, v_a_358_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(lean_object* v_msgData_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msgData_361_, v___y_363_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___boxed(lean_object* v_msgData_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(v_msgData_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(lean_object* v_00_u03b1_371_, lean_object* v_msg_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v_msg_372_, v___y_373_, v___y_374_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___boxed(lean_object* v_00_u03b1_377_, lean_object* v_msg_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(v_00_u03b1_377_, v_msg_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(lean_object* v_00_u03b1_383_, lean_object* v_ref_384_, lean_object* v_msg_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_ref_384_, v_msg_385_, v___y_386_, v___y_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___boxed(lean_object* v_00_u03b1_390_, lean_object* v_ref_391_, lean_object* v_msg_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(v_00_u03b1_390_, v_ref_391_, v_msg_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v_ref_391_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(lean_object* v_msgData_397_, lean_object* v_macroStack_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(v_msgData_397_, v_macroStack_398_, v___y_400_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___boxed(lean_object* v_msgData_403_, lean_object* v_macroStack_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(v_msgData_403_, v_macroStack_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1(){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_420_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_421_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4));
v___x_422_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_423_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed), 4, 0);
v___x_424_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_420_, v___x_421_, v___x_422_, v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3(){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_454_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6));
v___x_455_ = l_Lean_addBuiltinDeclarationRanges(v___x_453_, v___x_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object* v_a_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
return v_res_457_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0));
v___x_460_ = l_Lean_stringToMessageData(v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(lean_object* v_stx_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_val_473_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = l_Lean_Syntax_getArg(v_stx_462_, v___x_480_);
switch(lean_obj_tag(v___x_481_))
{
case 2:
{
lean_object* v_val_482_; 
lean_dec(v_stx_462_);
v_val_482_ = lean_ctor_get(v___x_481_, 1);
lean_inc_ref(v_val_482_);
lean_dec_ref_known(v___x_481_, 2);
v_val_473_ = v_val_482_;
goto v___jp_472_;
}
case 1:
{
lean_object* v_kind_483_; 
v_kind_483_ = lean_ctor_get(v___x_481_, 1);
lean_inc(v_kind_483_);
if (lean_obj_tag(v_kind_483_) == 1)
{
lean_object* v_pre_484_; 
v_pre_484_ = lean_ctor_get(v_kind_483_, 0);
lean_inc(v_pre_484_);
if (lean_obj_tag(v_pre_484_) == 1)
{
lean_object* v_pre_485_; 
v_pre_485_ = lean_ctor_get(v_pre_484_, 0);
lean_inc(v_pre_485_);
if (lean_obj_tag(v_pre_485_) == 1)
{
lean_object* v_pre_486_; 
v_pre_486_ = lean_ctor_get(v_pre_485_, 0);
lean_inc(v_pre_486_);
if (lean_obj_tag(v_pre_486_) == 1)
{
lean_object* v_pre_487_; 
v_pre_487_ = lean_ctor_get(v_pre_486_, 0);
if (lean_obj_tag(v_pre_487_) == 0)
{
lean_object* v_str_488_; lean_object* v_str_489_; lean_object* v_str_490_; lean_object* v_str_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v_str_488_ = lean_ctor_get(v_kind_483_, 1);
lean_inc_ref(v_str_488_);
lean_dec_ref_known(v_kind_483_, 2);
v_str_489_ = lean_ctor_get(v_pre_484_, 1);
lean_inc_ref(v_str_489_);
lean_dec_ref_known(v_pre_484_, 2);
v_str_490_ = lean_ctor_get(v_pre_485_, 1);
lean_inc_ref(v_str_490_);
lean_dec_ref_known(v_pre_485_, 2);
v_str_491_ = lean_ctor_get(v_pre_486_, 1);
lean_inc_ref(v_str_491_);
lean_dec_ref_known(v_pre_486_, 2);
v___x_492_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0));
v___x_493_ = lean_string_dec_eq(v_str_491_, v___x_492_);
lean_dec_ref(v_str_491_);
if (v___x_493_ == 0)
{
lean_dec_ref(v_str_490_);
lean_dec_ref(v_str_489_);
lean_dec_ref(v_str_488_);
lean_dec_ref_known(v___x_481_, 3);
goto v___jp_466_;
}
else
{
lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_494_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1));
v___x_495_ = lean_string_dec_eq(v_str_490_, v___x_494_);
lean_dec_ref(v_str_490_);
if (v___x_495_ == 0)
{
lean_dec_ref(v_str_489_);
lean_dec_ref(v_str_488_);
lean_dec_ref_known(v___x_481_, 3);
goto v___jp_466_;
}
else
{
lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_496_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2));
v___x_497_ = lean_string_dec_eq(v_str_489_, v___x_496_);
lean_dec_ref(v_str_489_);
if (v___x_497_ == 0)
{
lean_dec_ref(v_str_488_);
lean_dec_ref_known(v___x_481_, 3);
goto v___jp_466_;
}
else
{
lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_498_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2));
v___x_499_ = lean_string_dec_eq(v_str_488_, v___x_498_);
lean_dec_ref(v_str_488_);
if (v___x_499_ == 0)
{
lean_dec_ref_known(v___x_481_, 3);
goto v___jp_466_;
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = l_Lean_Syntax_getArg(v___x_481_, v___x_500_);
lean_dec_ref_known(v___x_481_, 3);
if (lean_obj_tag(v___x_501_) == 2)
{
lean_object* v_val_502_; 
lean_dec(v_stx_462_);
v_val_502_ = lean_ctor_get(v___x_501_, 1);
lean_inc_ref(v_val_502_);
lean_dec_ref_known(v___x_501_, 2);
v_val_473_ = v_val_502_;
goto v___jp_472_;
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec(v___x_501_);
v___x_503_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1);
lean_inc(v_stx_462_);
v___x_504_ = l_Lean_MessageData_ofSyntax(v_stx_462_);
v___x_505_ = l_Lean_indentD(v___x_504_);
v___x_506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_503_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_stx_462_, v___x_506_, v___y_463_, v___y_464_);
lean_dec(v_stx_462_);
return v___x_507_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_486_, 2);
lean_dec_ref_known(v_pre_485_, 2);
lean_dec_ref_known(v_pre_484_, 2);
lean_dec_ref_known(v_kind_483_, 2);
lean_dec_ref_known(v___x_481_, 3);
goto v___jp_466_;
}
}
else
{
lean_dec(v_pre_486_);
lean_dec_ref_known(v_pre_485_, 2);
lean_dec_ref_known(v_pre_484_, 2);
lean_dec_ref_known(v_kind_483_, 2);
lean_dec_ref_known(v___x_481_, 3);
goto v___jp_466_;
}
}
else
{
lean_dec_ref_known(v_pre_484_, 2);
lean_dec(v_pre_485_);
lean_dec_ref_known(v_kind_483_, 2);
lean_dec_ref_known(v___x_481_, 3);
goto v___jp_466_;
}
}
else
{
lean_dec(v_pre_484_);
lean_dec_ref_known(v_kind_483_, 2);
lean_dec_ref_known(v___x_481_, 3);
goto v___jp_466_;
}
}
else
{
lean_dec_ref_known(v___x_481_, 3);
lean_dec(v_kind_483_);
goto v___jp_466_;
}
}
default: 
{
lean_dec(v___x_481_);
goto v___jp_466_;
}
}
v___jp_466_:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_467_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1);
lean_inc(v_stx_462_);
v___x_468_ = l_Lean_MessageData_ofSyntax(v_stx_462_);
v___x_469_ = l_Lean_indentD(v___x_468_);
v___x_470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_467_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___x_471_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_stx_462_, v___x_470_, v___y_463_, v___y_464_);
lean_dec(v_stx_462_);
return v___x_471_;
}
v___jp_472_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_string_utf8_byte_size(v_val_473_);
v___x_476_ = lean_unsigned_to_nat(2u);
v___x_477_ = lean_nat_sub(v___x_475_, v___x_476_);
v___x_478_ = lean_string_utf8_extract(v_val_473_, v___x_474_, v___x_477_);
lean_dec(v___x_477_);
lean_dec_ref(v_val_473_);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___boxed(lean_object* v_stx_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(v_stx_508_, v___y_509_, v___y_510_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
return v_res_512_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0));
v___x_515_ = l_Lean_stringToMessageData(v___x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(lean_object* v_x_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v_a_533_; lean_object* v_doc_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_601_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
lean_inc(v_x_525_);
v___x_602_ = l_Lean_Syntax_isOfKind(v_x_525_, v___x_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; lean_object* v___x_604_; 
lean_dec(v_x_525_);
v___x_603_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_604_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_603_, v_a_526_, v_a_527_);
return v___x_604_;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_605_ = lean_unsigned_to_nat(0u);
v___x_606_ = l_Lean_Syntax_getArg(v_x_525_, v___x_605_);
v___x_607_ = l_Lean_Syntax_isNone(v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_606_);
v___x_609_ = l_Lean_Syntax_matchesNull(v___x_606_, v___x_608_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
lean_dec(v___x_606_);
lean_dec(v_x_525_);
v___x_610_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_611_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_610_, v_a_526_, v_a_527_);
return v___x_611_;
}
else
{
lean_object* v_doc_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v_doc_612_ = l_Lean_Syntax_getArg(v___x_606_, v___x_605_);
lean_dec(v___x_606_);
v___x_613_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8));
lean_inc(v_doc_612_);
v___x_614_ = l_Lean_Syntax_isOfKind(v_doc_612_, v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; 
lean_dec(v_doc_612_);
lean_dec(v_x_525_);
v___x_615_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_616_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_615_, v_a_526_, v_a_527_);
return v___x_616_;
}
else
{
lean_object* v___x_617_; 
v___x_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_617_, 0, v_doc_612_);
v_doc_567_ = v___x_617_;
v___y_568_ = v_a_526_;
v___y_569_ = v_a_527_;
goto v___jp_566_;
}
}
}
else
{
lean_object* v___x_618_; 
lean_dec(v___x_606_);
v___x_618_ = lean_box(0);
v_doc_567_ = v___x_618_;
v___y_568_ = v_a_526_;
v___y_569_ = v_a_527_;
goto v___jp_566_;
}
}
v___jp_529_:
{
lean_object* v___x_534_; lean_object* v_env_535_; lean_object* v_messages_536_; lean_object* v_scopes_537_; lean_object* v_usedQuotCtxts_538_; lean_object* v_nextMacroScope_539_; lean_object* v_maxRecDepth_540_; lean_object* v_ngen_541_; lean_object* v_auxDeclNGen_542_; lean_object* v_infoState_543_; lean_object* v_traceState_544_; lean_object* v_snapshotTasks_545_; lean_object* v_prevLinterStates_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_565_; 
v___x_534_ = lean_st_ref_take(v___y_531_);
v_env_535_ = lean_ctor_get(v___x_534_, 0);
v_messages_536_ = lean_ctor_get(v___x_534_, 1);
v_scopes_537_ = lean_ctor_get(v___x_534_, 2);
v_usedQuotCtxts_538_ = lean_ctor_get(v___x_534_, 3);
v_nextMacroScope_539_ = lean_ctor_get(v___x_534_, 4);
v_maxRecDepth_540_ = lean_ctor_get(v___x_534_, 5);
v_ngen_541_ = lean_ctor_get(v___x_534_, 6);
v_auxDeclNGen_542_ = lean_ctor_get(v___x_534_, 7);
v_infoState_543_ = lean_ctor_get(v___x_534_, 8);
v_traceState_544_ = lean_ctor_get(v___x_534_, 9);
v_snapshotTasks_545_ = lean_ctor_get(v___x_534_, 10);
v_prevLinterStates_546_ = lean_ctor_get(v___x_534_, 11);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_565_ == 0)
{
v___x_548_ = v___x_534_;
v_isShared_549_ = v_isSharedCheck_565_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_prevLinterStates_546_);
lean_inc(v_snapshotTasks_545_);
lean_inc(v_traceState_544_);
lean_inc(v_infoState_543_);
lean_inc(v_auxDeclNGen_542_);
lean_inc(v_ngen_541_);
lean_inc(v_maxRecDepth_540_);
lean_inc(v_nextMacroScope_539_);
lean_inc(v_usedQuotCtxts_538_);
lean_inc(v_scopes_537_);
lean_inc(v_messages_536_);
lean_inc(v_env_535_);
lean_dec(v___x_534_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_565_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v_toEnvExtension_551_; lean_object* v_asyncMode_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_550_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_551_ = lean_ctor_get(v___x_550_, 0);
v_asyncMode_552_ = lean_ctor_get(v_toEnvExtension_551_, 2);
v___x_553_ = l_Lean_TSyntax_getId(v___y_532_);
lean_dec(v___y_532_);
v___x_554_ = l_Lean_TSyntax_getString(v___y_530_);
lean_dec(v___y_530_);
v___x_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set(v___x_555_, 1, v_a_533_);
v___x_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_553_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = lean_box(0);
v___x_558_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_550_, v_env_535_, v___x_556_, v_asyncMode_552_, v___x_557_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_558_);
v___x_560_ = v___x_548_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_messages_536_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v_scopes_537_);
lean_ctor_set(v_reuseFailAlloc_564_, 3, v_usedQuotCtxts_538_);
lean_ctor_set(v_reuseFailAlloc_564_, 4, v_nextMacroScope_539_);
lean_ctor_set(v_reuseFailAlloc_564_, 5, v_maxRecDepth_540_);
lean_ctor_set(v_reuseFailAlloc_564_, 6, v_ngen_541_);
lean_ctor_set(v_reuseFailAlloc_564_, 7, v_auxDeclNGen_542_);
lean_ctor_set(v_reuseFailAlloc_564_, 8, v_infoState_543_);
lean_ctor_set(v_reuseFailAlloc_564_, 9, v_traceState_544_);
lean_ctor_set(v_reuseFailAlloc_564_, 10, v_snapshotTasks_545_);
lean_ctor_set(v_reuseFailAlloc_564_, 11, v_prevLinterStates_546_);
v___x_560_ = v_reuseFailAlloc_564_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_561_ = lean_st_ref_put(v___y_531_, v___x_560_);
v___x_562_ = lean_box(0);
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
}
}
v___jp_566_:
{
lean_object* v___x_570_; lean_object* v_tag_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_570_ = lean_unsigned_to_nat(2u);
v_tag_571_ = l_Lean_Syntax_getArg(v_x_525_, v___x_570_);
v___x_572_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10));
lean_inc(v_tag_571_);
v___x_573_ = l_Lean_Syntax_isOfKind(v_tag_571_, v___x_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec(v_tag_571_);
lean_dec(v_doc_567_);
lean_dec(v_x_525_);
v___x_574_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_575_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_574_, v___y_568_, v___y_569_);
return v___x_575_;
}
else
{
lean_object* v___x_576_; lean_object* v_user_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_576_ = lean_unsigned_to_nat(3u);
v_user_577_ = l_Lean_Syntax_getArg(v_x_525_, v___x_576_);
lean_dec(v_x_525_);
v___x_578_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3));
lean_inc(v_user_577_);
v___x_579_ = l_Lean_Syntax_isOfKind(v_user_577_, v___x_578_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v_user_577_);
lean_dec(v_tag_571_);
lean_dec(v_doc_567_);
v___x_580_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_581_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_580_, v___y_568_, v___y_569_);
return v___x_581_;
}
else
{
if (lean_obj_tag(v_doc_567_) == 0)
{
lean_object* v___x_582_; 
v___x_582_ = lean_box(0);
v___y_530_ = v_user_577_;
v___y_531_ = v___y_569_;
v___y_532_ = v_tag_571_;
v_a_533_ = v___x_582_;
goto v___jp_529_;
}
else
{
lean_object* v_val_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_600_; 
v_val_583_ = lean_ctor_get(v_doc_567_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v_doc_567_);
if (v_isSharedCheck_600_ == 0)
{
v___x_585_ = v_doc_567_;
v_isShared_586_ = v_isSharedCheck_600_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_val_583_);
lean_dec(v_doc_567_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_600_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(v_val_583_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_590_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_587_, 1);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v_a_588_);
v___x_590_ = v___x_585_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
v___y_530_ = v_user_577_;
v___y_531_ = v___y_569_;
v___y_532_ = v_tag_571_;
v_a_533_ = v___x_590_;
goto v___jp_529_;
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_del_object(v___x_585_);
lean_dec(v_user_577_);
lean_dec(v_tag_571_);
v_a_592_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_587_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_587_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed(lean_object* v_x_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(v_x_619_, v_a_620_, v_a_621_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1(){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_632_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_633_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
v___x_634_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_635_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed), 4, 0);
v___x_636_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_632_, v___x_633_, v___x_634_, v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object* v_a_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3(){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_666_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6));
v___x_667_ = l_Lean_addBuiltinDeclarationRanges(v___x_665_, v___x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(lean_object* v___x_670_, lean_object* v_x_671_){
_start:
{
if (lean_obj_tag(v_x_671_) == 0)
{
lean_object* v___x_672_; 
v___x_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_670_);
return v___x_672_;
}
else
{
lean_dec_ref(v___x_670_);
lean_inc_ref(v_x_671_);
return v_x_671_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_673_, lean_object* v_x_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_673_, v_x_674_);
lean_dec(v_x_674_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(lean_object* v___x_676_, lean_object* v_k_677_, lean_object* v_t_678_){
_start:
{
if (lean_obj_tag(v_t_678_) == 0)
{
lean_object* v_size_679_; lean_object* v_k_680_; lean_object* v_v_681_; lean_object* v_l_682_; lean_object* v_r_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_1009_; 
v_size_679_ = lean_ctor_get(v_t_678_, 0);
v_k_680_ = lean_ctor_get(v_t_678_, 1);
v_v_681_ = lean_ctor_get(v_t_678_, 2);
v_l_682_ = lean_ctor_get(v_t_678_, 3);
v_r_683_ = lean_ctor_get(v_t_678_, 4);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_t_678_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_685_ = v_t_678_;
v_isShared_686_ = v_isSharedCheck_1009_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_r_683_);
lean_inc(v_l_682_);
lean_inc(v_v_681_);
lean_inc(v_k_680_);
lean_inc(v_size_679_);
lean_dec(v_t_678_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_1009_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
uint8_t v___x_687_; 
v___x_687_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_677_, v_k_680_);
switch(v___x_687_)
{
case 0:
{
lean_object* v_impl_688_; lean_object* v___x_689_; 
lean_del_object(v___x_685_);
lean_dec(v_size_679_);
v_impl_688_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_676_, v_k_677_, v_l_682_);
v___x_689_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_680_, v_v_681_, v_impl_688_, v_r_683_);
return v___x_689_;
}
case 1:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
lean_dec(v_k_680_);
v___x_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_690_, 0, v_v_681_);
v___x_691_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_676_, v___x_690_);
lean_dec_ref_known(v___x_690_, 1);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_del_object(v___x_685_);
lean_dec(v_size_679_);
lean_dec(v_k_677_);
if (lean_obj_tag(v_l_682_) == 0)
{
if (lean_obj_tag(v_r_683_) == 0)
{
lean_object* v_size_692_; lean_object* v_k_693_; lean_object* v_v_694_; lean_object* v_l_695_; lean_object* v_r_696_; lean_object* v_size_697_; lean_object* v_k_698_; lean_object* v_v_699_; lean_object* v_l_700_; lean_object* v_r_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v_size_692_ = lean_ctor_get(v_l_682_, 0);
v_k_693_ = lean_ctor_get(v_l_682_, 1);
v_v_694_ = lean_ctor_get(v_l_682_, 2);
v_l_695_ = lean_ctor_get(v_l_682_, 3);
v_r_696_ = lean_ctor_get(v_l_682_, 4);
lean_inc(v_r_696_);
v_size_697_ = lean_ctor_get(v_r_683_, 0);
v_k_698_ = lean_ctor_get(v_r_683_, 1);
v_v_699_ = lean_ctor_get(v_r_683_, 2);
v_l_700_ = lean_ctor_get(v_r_683_, 3);
lean_inc(v_l_700_);
v_r_701_ = lean_ctor_get(v_r_683_, 4);
v___x_702_ = lean_unsigned_to_nat(1u);
v___x_703_ = lean_nat_dec_lt(v_size_692_, v_size_697_);
if (v___x_703_ == 0)
{
lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_839_; 
lean_inc(v_l_695_);
lean_inc(v_v_694_);
lean_inc(v_k_693_);
v_isSharedCheck_839_ = !lean_is_exclusive(v_l_682_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; lean_object* v_unused_841_; lean_object* v_unused_842_; lean_object* v_unused_843_; lean_object* v_unused_844_; 
v_unused_840_ = lean_ctor_get(v_l_682_, 4);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v_l_682_, 3);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_l_682_, 2);
lean_dec(v_unused_842_);
v_unused_843_ = lean_ctor_get(v_l_682_, 1);
lean_dec(v_unused_843_);
v_unused_844_ = lean_ctor_get(v_l_682_, 0);
lean_dec(v_unused_844_);
v___x_705_ = v_l_682_;
v_isShared_706_ = v_isSharedCheck_839_;
goto v_resetjp_704_;
}
else
{
lean_dec(v_l_682_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_839_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v_tree_708_; 
v___x_707_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_693_, v_v_694_, v_l_695_, v_r_696_);
v_tree_708_ = lean_ctor_get(v___x_707_, 2);
lean_inc(v_tree_708_);
if (lean_obj_tag(v_tree_708_) == 0)
{
lean_object* v_k_709_; lean_object* v_v_710_; lean_object* v_size_711_; lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v_k_709_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_k_709_);
v_v_710_ = lean_ctor_get(v___x_707_, 1);
lean_inc(v_v_710_);
lean_dec_ref(v___x_707_);
v_size_711_ = lean_ctor_get(v_tree_708_, 0);
v___x_712_ = lean_unsigned_to_nat(3u);
v___x_713_ = lean_nat_mul(v___x_712_, v_size_711_);
v___x_714_ = lean_nat_dec_lt(v___x_713_, v_size_697_);
lean_dec(v___x_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_718_; 
lean_dec(v_l_700_);
v___x_715_ = lean_nat_add(v___x_702_, v_size_711_);
v___x_716_ = lean_nat_add(v___x_715_, v_size_697_);
lean_dec(v___x_715_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 4, v_r_683_);
lean_ctor_set(v___x_705_, 3, v_tree_708_);
lean_ctor_set(v___x_705_, 2, v_v_710_);
lean_ctor_set(v___x_705_, 1, v_k_709_);
lean_ctor_set(v___x_705_, 0, v___x_716_);
v___x_718_ = v___x_705_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_k_709_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_v_710_);
lean_ctor_set(v_reuseFailAlloc_719_, 3, v_tree_708_);
lean_ctor_set(v_reuseFailAlloc_719_, 4, v_r_683_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
else
{
lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_774_; 
lean_inc(v_r_701_);
lean_inc(v_v_699_);
lean_inc(v_k_698_);
lean_inc(v_size_697_);
v_isSharedCheck_774_ = !lean_is_exclusive(v_r_683_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; lean_object* v_unused_776_; lean_object* v_unused_777_; lean_object* v_unused_778_; lean_object* v_unused_779_; 
v_unused_775_ = lean_ctor_get(v_r_683_, 4);
lean_dec(v_unused_775_);
v_unused_776_ = lean_ctor_get(v_r_683_, 3);
lean_dec(v_unused_776_);
v_unused_777_ = lean_ctor_get(v_r_683_, 2);
lean_dec(v_unused_777_);
v_unused_778_ = lean_ctor_get(v_r_683_, 1);
lean_dec(v_unused_778_);
v_unused_779_ = lean_ctor_get(v_r_683_, 0);
lean_dec(v_unused_779_);
v___x_721_ = v_r_683_;
v_isShared_722_ = v_isSharedCheck_774_;
goto v_resetjp_720_;
}
else
{
lean_dec(v_r_683_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_774_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v_size_723_; lean_object* v_k_724_; lean_object* v_v_725_; lean_object* v_l_726_; lean_object* v_r_727_; lean_object* v_size_728_; lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v_size_723_ = lean_ctor_get(v_l_700_, 0);
v_k_724_ = lean_ctor_get(v_l_700_, 1);
v_v_725_ = lean_ctor_get(v_l_700_, 2);
v_l_726_ = lean_ctor_get(v_l_700_, 3);
v_r_727_ = lean_ctor_get(v_l_700_, 4);
v_size_728_ = lean_ctor_get(v_r_701_, 0);
v___x_729_ = lean_unsigned_to_nat(2u);
v___x_730_ = lean_nat_mul(v___x_729_, v_size_728_);
v___x_731_ = lean_nat_dec_lt(v_size_723_, v___x_730_);
lean_dec(v___x_730_);
if (v___x_731_ == 0)
{
lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_759_; 
lean_inc(v_r_727_);
lean_inc(v_l_726_);
lean_inc(v_v_725_);
lean_inc(v_k_724_);
v_isSharedCheck_759_ = !lean_is_exclusive(v_l_700_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; lean_object* v_unused_761_; lean_object* v_unused_762_; lean_object* v_unused_763_; lean_object* v_unused_764_; 
v_unused_760_ = lean_ctor_get(v_l_700_, 4);
lean_dec(v_unused_760_);
v_unused_761_ = lean_ctor_get(v_l_700_, 3);
lean_dec(v_unused_761_);
v_unused_762_ = lean_ctor_get(v_l_700_, 2);
lean_dec(v_unused_762_);
v_unused_763_ = lean_ctor_get(v_l_700_, 1);
lean_dec(v_unused_763_);
v_unused_764_ = lean_ctor_get(v_l_700_, 0);
lean_dec(v_unused_764_);
v___x_733_ = v_l_700_;
v_isShared_734_ = v_isSharedCheck_759_;
goto v_resetjp_732_;
}
else
{
lean_dec(v_l_700_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_759_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_749_; 
v___x_735_ = lean_nat_add(v___x_702_, v_size_711_);
v___x_736_ = lean_nat_add(v___x_735_, v_size_697_);
lean_dec(v_size_697_);
if (lean_obj_tag(v_l_726_) == 0)
{
lean_object* v_size_757_; 
v_size_757_ = lean_ctor_get(v_l_726_, 0);
lean_inc(v_size_757_);
v___y_749_ = v_size_757_;
goto v___jp_748_;
}
else
{
lean_object* v___x_758_; 
v___x_758_ = lean_unsigned_to_nat(0u);
v___y_749_ = v___x_758_;
goto v___jp_748_;
}
v___jp_737_:
{
lean_object* v___x_741_; lean_object* v___x_743_; 
v___x_741_ = lean_nat_add(v___y_738_, v___y_740_);
lean_dec(v___y_740_);
lean_dec(v___y_738_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 4, v_r_701_);
lean_ctor_set(v___x_733_, 3, v_r_727_);
lean_ctor_set(v___x_733_, 2, v_v_699_);
lean_ctor_set(v___x_733_, 1, v_k_698_);
lean_ctor_set(v___x_733_, 0, v___x_741_);
v___x_743_ = v___x_733_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_k_698_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_v_699_);
lean_ctor_set(v_reuseFailAlloc_747_, 3, v_r_727_);
lean_ctor_set(v_reuseFailAlloc_747_, 4, v_r_701_);
v___x_743_ = v_reuseFailAlloc_747_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_745_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 4, v___x_743_);
lean_ctor_set(v___x_721_, 3, v___y_739_);
lean_ctor_set(v___x_721_, 2, v_v_725_);
lean_ctor_set(v___x_721_, 1, v_k_724_);
lean_ctor_set(v___x_721_, 0, v___x_736_);
v___x_745_ = v___x_721_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_736_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_k_724_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_v_725_);
lean_ctor_set(v_reuseFailAlloc_746_, 3, v___y_739_);
lean_ctor_set(v_reuseFailAlloc_746_, 4, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
v___jp_748_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = lean_nat_add(v___x_735_, v___y_749_);
lean_dec(v___y_749_);
lean_dec(v___x_735_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 4, v_l_726_);
lean_ctor_set(v___x_705_, 3, v_tree_708_);
lean_ctor_set(v___x_705_, 2, v_v_710_);
lean_ctor_set(v___x_705_, 1, v_k_709_);
lean_ctor_set(v___x_705_, 0, v___x_750_);
v___x_752_ = v___x_705_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_k_709_);
lean_ctor_set(v_reuseFailAlloc_756_, 2, v_v_710_);
lean_ctor_set(v_reuseFailAlloc_756_, 3, v_tree_708_);
lean_ctor_set(v_reuseFailAlloc_756_, 4, v_l_726_);
v___x_752_ = v_reuseFailAlloc_756_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_753_; 
v___x_753_ = lean_nat_add(v___x_702_, v_size_728_);
if (lean_obj_tag(v_r_727_) == 0)
{
lean_object* v_size_754_; 
v_size_754_ = lean_ctor_get(v_r_727_, 0);
lean_inc(v_size_754_);
v___y_738_ = v___x_753_;
v___y_739_ = v___x_752_;
v___y_740_ = v_size_754_;
goto v___jp_737_;
}
else
{
lean_object* v___x_755_; 
v___x_755_ = lean_unsigned_to_nat(0u);
v___y_738_ = v___x_753_;
v___y_739_ = v___x_752_;
v___y_740_ = v___x_755_;
goto v___jp_737_;
}
}
}
}
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_769_; 
v___x_765_ = lean_nat_add(v___x_702_, v_size_711_);
v___x_766_ = lean_nat_add(v___x_765_, v_size_697_);
lean_dec(v_size_697_);
v___x_767_ = lean_nat_add(v___x_765_, v_size_723_);
lean_dec(v___x_765_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 4, v_l_700_);
lean_ctor_set(v___x_721_, 3, v_tree_708_);
lean_ctor_set(v___x_721_, 2, v_v_710_);
lean_ctor_set(v___x_721_, 1, v_k_709_);
lean_ctor_set(v___x_721_, 0, v___x_767_);
v___x_769_ = v___x_721_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_k_709_);
lean_ctor_set(v_reuseFailAlloc_773_, 2, v_v_710_);
lean_ctor_set(v_reuseFailAlloc_773_, 3, v_tree_708_);
lean_ctor_set(v_reuseFailAlloc_773_, 4, v_l_700_);
v___x_769_ = v_reuseFailAlloc_773_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_771_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 4, v_r_701_);
lean_ctor_set(v___x_705_, 3, v___x_769_);
lean_ctor_set(v___x_705_, 2, v_v_699_);
lean_ctor_set(v___x_705_, 1, v_k_698_);
lean_ctor_set(v___x_705_, 0, v___x_766_);
v___x_771_ = v___x_705_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_k_698_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v_v_699_);
lean_ctor_set(v_reuseFailAlloc_772_, 3, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_772_, 4, v_r_701_);
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
}
else
{
lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_833_; 
lean_inc(v_r_701_);
lean_inc(v_v_699_);
lean_inc(v_k_698_);
lean_inc(v_size_697_);
v_isSharedCheck_833_ = !lean_is_exclusive(v_r_683_);
if (v_isSharedCheck_833_ == 0)
{
lean_object* v_unused_834_; lean_object* v_unused_835_; lean_object* v_unused_836_; lean_object* v_unused_837_; lean_object* v_unused_838_; 
v_unused_834_ = lean_ctor_get(v_r_683_, 4);
lean_dec(v_unused_834_);
v_unused_835_ = lean_ctor_get(v_r_683_, 3);
lean_dec(v_unused_835_);
v_unused_836_ = lean_ctor_get(v_r_683_, 2);
lean_dec(v_unused_836_);
v_unused_837_ = lean_ctor_get(v_r_683_, 1);
lean_dec(v_unused_837_);
v_unused_838_ = lean_ctor_get(v_r_683_, 0);
lean_dec(v_unused_838_);
v___x_781_ = v_r_683_;
v_isShared_782_ = v_isSharedCheck_833_;
goto v_resetjp_780_;
}
else
{
lean_dec(v_r_683_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_833_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
if (lean_obj_tag(v_l_700_) == 0)
{
if (lean_obj_tag(v_r_701_) == 0)
{
lean_object* v_k_783_; lean_object* v_v_784_; lean_object* v_size_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
v_k_783_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_k_783_);
v_v_784_ = lean_ctor_get(v___x_707_, 1);
lean_inc(v_v_784_);
lean_dec_ref(v___x_707_);
v_size_785_ = lean_ctor_get(v_l_700_, 0);
v___x_786_ = lean_nat_add(v___x_702_, v_size_697_);
lean_dec(v_size_697_);
v___x_787_ = lean_nat_add(v___x_702_, v_size_785_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 4, v_l_700_);
lean_ctor_set(v___x_781_, 3, v_tree_708_);
lean_ctor_set(v___x_781_, 2, v_v_784_);
lean_ctor_set(v___x_781_, 1, v_k_783_);
lean_ctor_set(v___x_781_, 0, v___x_787_);
v___x_789_ = v___x_781_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_k_783_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v_v_784_);
lean_ctor_set(v_reuseFailAlloc_793_, 3, v_tree_708_);
lean_ctor_set(v_reuseFailAlloc_793_, 4, v_l_700_);
v___x_789_ = v_reuseFailAlloc_793_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_791_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 4, v_r_701_);
lean_ctor_set(v___x_705_, 3, v___x_789_);
lean_ctor_set(v___x_705_, 2, v_v_699_);
lean_ctor_set(v___x_705_, 1, v_k_698_);
lean_ctor_set(v___x_705_, 0, v___x_786_);
v___x_791_ = v___x_705_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_k_698_);
lean_ctor_set(v_reuseFailAlloc_792_, 2, v_v_699_);
lean_ctor_set(v_reuseFailAlloc_792_, 3, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_792_, 4, v_r_701_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
else
{
lean_object* v_k_794_; lean_object* v_v_795_; lean_object* v_k_796_; lean_object* v_v_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_811_; 
lean_dec(v_size_697_);
v_k_794_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_k_794_);
v_v_795_ = lean_ctor_get(v___x_707_, 1);
lean_inc(v_v_795_);
lean_dec_ref(v___x_707_);
v_k_796_ = lean_ctor_get(v_l_700_, 1);
v_v_797_ = lean_ctor_get(v_l_700_, 2);
v_isSharedCheck_811_ = !lean_is_exclusive(v_l_700_);
if (v_isSharedCheck_811_ == 0)
{
lean_object* v_unused_812_; lean_object* v_unused_813_; lean_object* v_unused_814_; 
v_unused_812_ = lean_ctor_get(v_l_700_, 4);
lean_dec(v_unused_812_);
v_unused_813_ = lean_ctor_get(v_l_700_, 3);
lean_dec(v_unused_813_);
v_unused_814_ = lean_ctor_get(v_l_700_, 0);
lean_dec(v_unused_814_);
v___x_799_ = v_l_700_;
v_isShared_800_ = v_isSharedCheck_811_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_v_797_);
lean_inc(v_k_796_);
lean_dec(v_l_700_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_811_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_801_ = lean_unsigned_to_nat(3u);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 4, v_r_701_);
lean_ctor_set(v___x_799_, 3, v_r_701_);
lean_ctor_set(v___x_799_, 2, v_v_795_);
lean_ctor_set(v___x_799_, 1, v_k_794_);
lean_ctor_set(v___x_799_, 0, v___x_702_);
v___x_803_ = v___x_799_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_k_794_);
lean_ctor_set(v_reuseFailAlloc_810_, 2, v_v_795_);
lean_ctor_set(v_reuseFailAlloc_810_, 3, v_r_701_);
lean_ctor_set(v_reuseFailAlloc_810_, 4, v_r_701_);
v___x_803_ = v_reuseFailAlloc_810_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_805_; 
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 3, v_r_701_);
lean_ctor_set(v___x_781_, 0, v___x_702_);
v___x_805_ = v___x_781_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_k_698_);
lean_ctor_set(v_reuseFailAlloc_809_, 2, v_v_699_);
lean_ctor_set(v_reuseFailAlloc_809_, 3, v_r_701_);
lean_ctor_set(v_reuseFailAlloc_809_, 4, v_r_701_);
v___x_805_ = v_reuseFailAlloc_809_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_807_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 4, v___x_805_);
lean_ctor_set(v___x_705_, 3, v___x_803_);
lean_ctor_set(v___x_705_, 2, v_v_797_);
lean_ctor_set(v___x_705_, 1, v_k_796_);
lean_ctor_set(v___x_705_, 0, v___x_801_);
v___x_807_ = v___x_705_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_k_796_);
lean_ctor_set(v_reuseFailAlloc_808_, 2, v_v_797_);
lean_ctor_set(v_reuseFailAlloc_808_, 3, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_808_, 4, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_701_) == 0)
{
lean_object* v_k_815_; lean_object* v_v_816_; lean_object* v___x_817_; lean_object* v___x_819_; 
lean_dec(v_size_697_);
v_k_815_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_k_815_);
v_v_816_ = lean_ctor_get(v___x_707_, 1);
lean_inc(v_v_816_);
lean_dec_ref(v___x_707_);
v___x_817_ = lean_unsigned_to_nat(3u);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 4, v_l_700_);
lean_ctor_set(v___x_781_, 2, v_v_816_);
lean_ctor_set(v___x_781_, 1, v_k_815_);
lean_ctor_set(v___x_781_, 0, v___x_702_);
v___x_819_ = v___x_781_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_k_815_);
lean_ctor_set(v_reuseFailAlloc_823_, 2, v_v_816_);
lean_ctor_set(v_reuseFailAlloc_823_, 3, v_l_700_);
lean_ctor_set(v_reuseFailAlloc_823_, 4, v_l_700_);
v___x_819_ = v_reuseFailAlloc_823_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_821_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 4, v_r_701_);
lean_ctor_set(v___x_705_, 3, v___x_819_);
lean_ctor_set(v___x_705_, 2, v_v_699_);
lean_ctor_set(v___x_705_, 1, v_k_698_);
lean_ctor_set(v___x_705_, 0, v___x_817_);
v___x_821_ = v___x_705_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_k_698_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v_v_699_);
lean_ctor_set(v_reuseFailAlloc_822_, 3, v___x_819_);
lean_ctor_set(v_reuseFailAlloc_822_, 4, v_r_701_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
else
{
lean_object* v_k_824_; lean_object* v_v_825_; lean_object* v___x_827_; 
v_k_824_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_k_824_);
v_v_825_ = lean_ctor_get(v___x_707_, 1);
lean_inc(v_v_825_);
lean_dec_ref(v___x_707_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 3, v_r_701_);
v___x_827_ = v___x_781_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_size_697_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_k_698_);
lean_ctor_set(v_reuseFailAlloc_832_, 2, v_v_699_);
lean_ctor_set(v_reuseFailAlloc_832_, 3, v_r_701_);
lean_ctor_set(v_reuseFailAlloc_832_, 4, v_r_701_);
v___x_827_ = v_reuseFailAlloc_832_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_828_ = lean_unsigned_to_nat(2u);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 4, v___x_827_);
lean_ctor_set(v___x_705_, 3, v_r_701_);
lean_ctor_set(v___x_705_, 2, v_v_825_);
lean_ctor_set(v___x_705_, 1, v_k_824_);
lean_ctor_set(v___x_705_, 0, v___x_828_);
v___x_830_ = v___x_705_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_k_824_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v_v_825_);
lean_ctor_set(v_reuseFailAlloc_831_, 3, v_r_701_);
lean_ctor_set(v_reuseFailAlloc_831_, 4, v___x_827_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
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
lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_997_; 
lean_inc(v_r_701_);
lean_inc(v_v_699_);
lean_inc(v_k_698_);
v_isSharedCheck_997_ = !lean_is_exclusive(v_r_683_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; lean_object* v_unused_999_; lean_object* v_unused_1000_; lean_object* v_unused_1001_; lean_object* v_unused_1002_; 
v_unused_998_ = lean_ctor_get(v_r_683_, 4);
lean_dec(v_unused_998_);
v_unused_999_ = lean_ctor_get(v_r_683_, 3);
lean_dec(v_unused_999_);
v_unused_1000_ = lean_ctor_get(v_r_683_, 2);
lean_dec(v_unused_1000_);
v_unused_1001_ = lean_ctor_get(v_r_683_, 1);
lean_dec(v_unused_1001_);
v_unused_1002_ = lean_ctor_get(v_r_683_, 0);
lean_dec(v_unused_1002_);
v___x_846_ = v_r_683_;
v_isShared_847_ = v_isSharedCheck_997_;
goto v_resetjp_845_;
}
else
{
lean_dec(v_r_683_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_997_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v_tree_849_; 
v___x_848_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_698_, v_v_699_, v_l_700_, v_r_701_);
v_tree_849_ = lean_ctor_get(v___x_848_, 2);
lean_inc(v_tree_849_);
if (lean_obj_tag(v_tree_849_) == 0)
{
lean_object* v_k_850_; lean_object* v_v_851_; lean_object* v_size_852_; lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v_k_850_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_k_850_);
v_v_851_ = lean_ctor_get(v___x_848_, 1);
lean_inc(v_v_851_);
lean_dec_ref(v___x_848_);
v_size_852_ = lean_ctor_get(v_tree_849_, 0);
v___x_853_ = lean_unsigned_to_nat(3u);
v___x_854_ = lean_nat_mul(v___x_853_, v_size_852_);
v___x_855_ = lean_nat_dec_lt(v___x_854_, v_size_692_);
lean_dec(v___x_854_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
lean_dec(v_r_696_);
v___x_856_ = lean_nat_add(v___x_702_, v_size_692_);
v___x_857_ = lean_nat_add(v___x_856_, v_size_852_);
lean_dec(v___x_856_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 4, v_tree_849_);
lean_ctor_set(v___x_846_, 3, v_l_682_);
lean_ctor_set(v___x_846_, 2, v_v_851_);
lean_ctor_set(v___x_846_, 1, v_k_850_);
lean_ctor_set(v___x_846_, 0, v___x_857_);
v___x_859_ = v___x_846_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_k_850_);
lean_ctor_set(v_reuseFailAlloc_860_, 2, v_v_851_);
lean_ctor_set(v_reuseFailAlloc_860_, 3, v_l_682_);
lean_ctor_set(v_reuseFailAlloc_860_, 4, v_tree_849_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
else
{
lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_926_; 
lean_inc(v_l_695_);
lean_inc(v_v_694_);
lean_inc(v_k_693_);
lean_inc(v_size_692_);
v_isSharedCheck_926_ = !lean_is_exclusive(v_l_682_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; lean_object* v_unused_928_; lean_object* v_unused_929_; lean_object* v_unused_930_; lean_object* v_unused_931_; 
v_unused_927_ = lean_ctor_get(v_l_682_, 4);
lean_dec(v_unused_927_);
v_unused_928_ = lean_ctor_get(v_l_682_, 3);
lean_dec(v_unused_928_);
v_unused_929_ = lean_ctor_get(v_l_682_, 2);
lean_dec(v_unused_929_);
v_unused_930_ = lean_ctor_get(v_l_682_, 1);
lean_dec(v_unused_930_);
v_unused_931_ = lean_ctor_get(v_l_682_, 0);
lean_dec(v_unused_931_);
v___x_862_ = v_l_682_;
v_isShared_863_ = v_isSharedCheck_926_;
goto v_resetjp_861_;
}
else
{
lean_dec(v_l_682_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_926_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v_size_864_; lean_object* v_size_865_; lean_object* v_k_866_; lean_object* v_v_867_; lean_object* v_l_868_; lean_object* v_r_869_; lean_object* v___x_870_; lean_object* v___x_871_; uint8_t v___x_872_; 
v_size_864_ = lean_ctor_get(v_l_695_, 0);
v_size_865_ = lean_ctor_get(v_r_696_, 0);
v_k_866_ = lean_ctor_get(v_r_696_, 1);
v_v_867_ = lean_ctor_get(v_r_696_, 2);
v_l_868_ = lean_ctor_get(v_r_696_, 3);
v_r_869_ = lean_ctor_get(v_r_696_, 4);
v___x_870_ = lean_unsigned_to_nat(2u);
v___x_871_ = lean_nat_mul(v___x_870_, v_size_864_);
v___x_872_ = lean_nat_dec_lt(v_size_865_, v___x_871_);
lean_dec(v___x_871_);
if (v___x_872_ == 0)
{
lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_910_; 
lean_inc(v_r_869_);
lean_inc(v_l_868_);
lean_inc(v_v_867_);
lean_inc(v_k_866_);
lean_del_object(v___x_862_);
v_isSharedCheck_910_ = !lean_is_exclusive(v_r_696_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; lean_object* v_unused_912_; lean_object* v_unused_913_; lean_object* v_unused_914_; lean_object* v_unused_915_; 
v_unused_911_ = lean_ctor_get(v_r_696_, 4);
lean_dec(v_unused_911_);
v_unused_912_ = lean_ctor_get(v_r_696_, 3);
lean_dec(v_unused_912_);
v_unused_913_ = lean_ctor_get(v_r_696_, 2);
lean_dec(v_unused_913_);
v_unused_914_ = lean_ctor_get(v_r_696_, 1);
lean_dec(v_unused_914_);
v_unused_915_ = lean_ctor_get(v_r_696_, 0);
lean_dec(v_unused_915_);
v___x_874_ = v_r_696_;
v_isShared_875_ = v_isSharedCheck_910_;
goto v_resetjp_873_;
}
else
{
lean_dec(v_r_696_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_910_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___x_898_; lean_object* v___y_900_; 
v___x_876_ = lean_nat_add(v___x_702_, v_size_692_);
lean_dec(v_size_692_);
v___x_877_ = lean_nat_add(v___x_876_, v_size_852_);
lean_dec(v___x_876_);
v___x_898_ = lean_nat_add(v___x_702_, v_size_864_);
if (lean_obj_tag(v_l_868_) == 0)
{
lean_object* v_size_908_; 
v_size_908_ = lean_ctor_get(v_l_868_, 0);
lean_inc(v_size_908_);
v___y_900_ = v_size_908_;
goto v___jp_899_;
}
else
{
lean_object* v___x_909_; 
v___x_909_ = lean_unsigned_to_nat(0u);
v___y_900_ = v___x_909_;
goto v___jp_899_;
}
v___jp_878_:
{
lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_882_ = lean_nat_add(v___y_879_, v___y_881_);
lean_dec(v___y_881_);
lean_dec(v___y_879_);
lean_inc_ref(v_tree_849_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 4, v_tree_849_);
lean_ctor_set(v___x_874_, 3, v_r_869_);
lean_ctor_set(v___x_874_, 2, v_v_851_);
lean_ctor_set(v___x_874_, 1, v_k_850_);
lean_ctor_set(v___x_874_, 0, v___x_882_);
v___x_884_ = v___x_874_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_k_850_);
lean_ctor_set(v_reuseFailAlloc_897_, 2, v_v_851_);
lean_ctor_set(v_reuseFailAlloc_897_, 3, v_r_869_);
lean_ctor_set(v_reuseFailAlloc_897_, 4, v_tree_849_);
v___x_884_ = v_reuseFailAlloc_897_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
v_isSharedCheck_891_ = !lean_is_exclusive(v_tree_849_);
if (v_isSharedCheck_891_ == 0)
{
lean_object* v_unused_892_; lean_object* v_unused_893_; lean_object* v_unused_894_; lean_object* v_unused_895_; lean_object* v_unused_896_; 
v_unused_892_ = lean_ctor_get(v_tree_849_, 4);
lean_dec(v_unused_892_);
v_unused_893_ = lean_ctor_get(v_tree_849_, 3);
lean_dec(v_unused_893_);
v_unused_894_ = lean_ctor_get(v_tree_849_, 2);
lean_dec(v_unused_894_);
v_unused_895_ = lean_ctor_get(v_tree_849_, 1);
lean_dec(v_unused_895_);
v_unused_896_ = lean_ctor_get(v_tree_849_, 0);
lean_dec(v_unused_896_);
v___x_886_ = v_tree_849_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_dec(v_tree_849_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 4, v___x_884_);
lean_ctor_set(v___x_886_, 3, v___y_880_);
lean_ctor_set(v___x_886_, 2, v_v_867_);
lean_ctor_set(v___x_886_, 1, v_k_866_);
lean_ctor_set(v___x_886_, 0, v___x_877_);
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_k_866_);
lean_ctor_set(v_reuseFailAlloc_890_, 2, v_v_867_);
lean_ctor_set(v_reuseFailAlloc_890_, 3, v___y_880_);
lean_ctor_set(v_reuseFailAlloc_890_, 4, v___x_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
v___jp_899_:
{
lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_901_ = lean_nat_add(v___x_898_, v___y_900_);
lean_dec(v___y_900_);
lean_dec(v___x_898_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 4, v_l_868_);
lean_ctor_set(v___x_846_, 3, v_l_695_);
lean_ctor_set(v___x_846_, 2, v_v_694_);
lean_ctor_set(v___x_846_, 1, v_k_693_);
lean_ctor_set(v___x_846_, 0, v___x_901_);
v___x_903_ = v___x_846_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_901_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_k_693_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v_v_694_);
lean_ctor_set(v_reuseFailAlloc_907_, 3, v_l_695_);
lean_ctor_set(v_reuseFailAlloc_907_, 4, v_l_868_);
v___x_903_ = v_reuseFailAlloc_907_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_904_; 
v___x_904_ = lean_nat_add(v___x_702_, v_size_852_);
if (lean_obj_tag(v_r_869_) == 0)
{
lean_object* v_size_905_; 
v_size_905_ = lean_ctor_get(v_r_869_, 0);
lean_inc(v_size_905_);
v___y_879_ = v___x_904_;
v___y_880_ = v___x_903_;
v___y_881_ = v_size_905_;
goto v___jp_878_;
}
else
{
lean_object* v___x_906_; 
v___x_906_ = lean_unsigned_to_nat(0u);
v___y_879_ = v___x_904_;
v___y_880_ = v___x_903_;
v___y_881_ = v___x_906_;
goto v___jp_878_;
}
}
}
}
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_916_ = lean_nat_add(v___x_702_, v_size_692_);
lean_dec(v_size_692_);
v___x_917_ = lean_nat_add(v___x_916_, v_size_852_);
lean_dec(v___x_916_);
v___x_918_ = lean_nat_add(v___x_702_, v_size_852_);
v___x_919_ = lean_nat_add(v___x_918_, v_size_865_);
lean_dec(v___x_918_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 4, v_tree_849_);
lean_ctor_set(v___x_846_, 3, v_r_696_);
lean_ctor_set(v___x_846_, 2, v_v_851_);
lean_ctor_set(v___x_846_, 1, v_k_850_);
lean_ctor_set(v___x_846_, 0, v___x_919_);
v___x_921_ = v___x_846_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_k_850_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v_v_851_);
lean_ctor_set(v_reuseFailAlloc_925_, 3, v_r_696_);
lean_ctor_set(v_reuseFailAlloc_925_, 4, v_tree_849_);
v___x_921_ = v_reuseFailAlloc_925_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_923_; 
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 4, v___x_921_);
lean_ctor_set(v___x_862_, 0, v___x_917_);
v___x_923_ = v___x_862_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_k_693_);
lean_ctor_set(v_reuseFailAlloc_924_, 2, v_v_694_);
lean_ctor_set(v_reuseFailAlloc_924_, 3, v_l_695_);
lean_ctor_set(v_reuseFailAlloc_924_, 4, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_695_) == 0)
{
lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_955_; 
lean_inc_ref(v_l_695_);
lean_inc(v_v_694_);
lean_inc(v_k_693_);
lean_inc(v_size_692_);
v_isSharedCheck_955_ = !lean_is_exclusive(v_l_682_);
if (v_isSharedCheck_955_ == 0)
{
lean_object* v_unused_956_; lean_object* v_unused_957_; lean_object* v_unused_958_; lean_object* v_unused_959_; lean_object* v_unused_960_; 
v_unused_956_ = lean_ctor_get(v_l_682_, 4);
lean_dec(v_unused_956_);
v_unused_957_ = lean_ctor_get(v_l_682_, 3);
lean_dec(v_unused_957_);
v_unused_958_ = lean_ctor_get(v_l_682_, 2);
lean_dec(v_unused_958_);
v_unused_959_ = lean_ctor_get(v_l_682_, 1);
lean_dec(v_unused_959_);
v_unused_960_ = lean_ctor_get(v_l_682_, 0);
lean_dec(v_unused_960_);
v___x_933_ = v_l_682_;
v_isShared_934_ = v_isSharedCheck_955_;
goto v_resetjp_932_;
}
else
{
lean_dec(v_l_682_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_955_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
if (lean_obj_tag(v_r_696_) == 0)
{
lean_object* v_k_935_; lean_object* v_v_936_; lean_object* v_size_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_941_; 
v_k_935_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_k_935_);
v_v_936_ = lean_ctor_get(v___x_848_, 1);
lean_inc(v_v_936_);
lean_dec_ref(v___x_848_);
v_size_937_ = lean_ctor_get(v_r_696_, 0);
v___x_938_ = lean_nat_add(v___x_702_, v_size_692_);
lean_dec(v_size_692_);
v___x_939_ = lean_nat_add(v___x_702_, v_size_937_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 4, v_tree_849_);
lean_ctor_set(v___x_846_, 3, v_r_696_);
lean_ctor_set(v___x_846_, 2, v_v_936_);
lean_ctor_set(v___x_846_, 1, v_k_935_);
lean_ctor_set(v___x_846_, 0, v___x_939_);
v___x_941_ = v___x_846_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_k_935_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v_v_936_);
lean_ctor_set(v_reuseFailAlloc_945_, 3, v_r_696_);
lean_ctor_set(v_reuseFailAlloc_945_, 4, v_tree_849_);
v___x_941_ = v_reuseFailAlloc_945_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_943_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 4, v___x_941_);
lean_ctor_set(v___x_933_, 0, v___x_938_);
v___x_943_ = v___x_933_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_k_693_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v_v_694_);
lean_ctor_set(v_reuseFailAlloc_944_, 3, v_l_695_);
lean_ctor_set(v_reuseFailAlloc_944_, 4, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
else
{
lean_object* v_k_946_; lean_object* v_v_947_; lean_object* v___x_948_; lean_object* v___x_950_; 
lean_dec(v_size_692_);
v_k_946_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_k_946_);
v_v_947_ = lean_ctor_get(v___x_848_, 1);
lean_inc(v_v_947_);
lean_dec_ref(v___x_848_);
v___x_948_ = lean_unsigned_to_nat(3u);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 4, v_r_696_);
lean_ctor_set(v___x_846_, 3, v_r_696_);
lean_ctor_set(v___x_846_, 2, v_v_947_);
lean_ctor_set(v___x_846_, 1, v_k_946_);
lean_ctor_set(v___x_846_, 0, v___x_702_);
v___x_950_ = v___x_846_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_k_946_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v_v_947_);
lean_ctor_set(v_reuseFailAlloc_954_, 3, v_r_696_);
lean_ctor_set(v_reuseFailAlloc_954_, 4, v_r_696_);
v___x_950_ = v_reuseFailAlloc_954_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_952_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 4, v___x_950_);
lean_ctor_set(v___x_933_, 0, v___x_948_);
v___x_952_ = v___x_933_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_k_693_);
lean_ctor_set(v_reuseFailAlloc_953_, 2, v_v_694_);
lean_ctor_set(v_reuseFailAlloc_953_, 3, v_l_695_);
lean_ctor_set(v_reuseFailAlloc_953_, 4, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_696_) == 0)
{
lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_985_; 
lean_inc(v_l_695_);
lean_inc(v_v_694_);
lean_inc(v_k_693_);
v_isSharedCheck_985_ = !lean_is_exclusive(v_l_682_);
if (v_isSharedCheck_985_ == 0)
{
lean_object* v_unused_986_; lean_object* v_unused_987_; lean_object* v_unused_988_; lean_object* v_unused_989_; lean_object* v_unused_990_; 
v_unused_986_ = lean_ctor_get(v_l_682_, 4);
lean_dec(v_unused_986_);
v_unused_987_ = lean_ctor_get(v_l_682_, 3);
lean_dec(v_unused_987_);
v_unused_988_ = lean_ctor_get(v_l_682_, 2);
lean_dec(v_unused_988_);
v_unused_989_ = lean_ctor_get(v_l_682_, 1);
lean_dec(v_unused_989_);
v_unused_990_ = lean_ctor_get(v_l_682_, 0);
lean_dec(v_unused_990_);
v___x_962_ = v_l_682_;
v_isShared_963_ = v_isSharedCheck_985_;
goto v_resetjp_961_;
}
else
{
lean_dec(v_l_682_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_985_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v_k_964_; lean_object* v_v_965_; lean_object* v_k_966_; lean_object* v_v_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_981_; 
v_k_964_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_k_964_);
v_v_965_ = lean_ctor_get(v___x_848_, 1);
lean_inc(v_v_965_);
lean_dec_ref(v___x_848_);
v_k_966_ = lean_ctor_get(v_r_696_, 1);
v_v_967_ = lean_ctor_get(v_r_696_, 2);
v_isSharedCheck_981_ = !lean_is_exclusive(v_r_696_);
if (v_isSharedCheck_981_ == 0)
{
lean_object* v_unused_982_; lean_object* v_unused_983_; lean_object* v_unused_984_; 
v_unused_982_ = lean_ctor_get(v_r_696_, 4);
lean_dec(v_unused_982_);
v_unused_983_ = lean_ctor_get(v_r_696_, 3);
lean_dec(v_unused_983_);
v_unused_984_ = lean_ctor_get(v_r_696_, 0);
lean_dec(v_unused_984_);
v___x_969_ = v_r_696_;
v_isShared_970_ = v_isSharedCheck_981_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_v_967_);
lean_inc(v_k_966_);
lean_dec(v_r_696_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_981_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_971_ = lean_unsigned_to_nat(3u);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 4, v_l_695_);
lean_ctor_set(v___x_969_, 3, v_l_695_);
lean_ctor_set(v___x_969_, 2, v_v_694_);
lean_ctor_set(v___x_969_, 1, v_k_693_);
lean_ctor_set(v___x_969_, 0, v___x_702_);
v___x_973_ = v___x_969_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v_k_693_);
lean_ctor_set(v_reuseFailAlloc_980_, 2, v_v_694_);
lean_ctor_set(v_reuseFailAlloc_980_, 3, v_l_695_);
lean_ctor_set(v_reuseFailAlloc_980_, 4, v_l_695_);
v___x_973_ = v_reuseFailAlloc_980_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_975_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 4, v_l_695_);
lean_ctor_set(v___x_846_, 3, v_l_695_);
lean_ctor_set(v___x_846_, 2, v_v_965_);
lean_ctor_set(v___x_846_, 1, v_k_964_);
lean_ctor_set(v___x_846_, 0, v___x_702_);
v___x_975_ = v___x_846_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_k_964_);
lean_ctor_set(v_reuseFailAlloc_979_, 2, v_v_965_);
lean_ctor_set(v_reuseFailAlloc_979_, 3, v_l_695_);
lean_ctor_set(v_reuseFailAlloc_979_, 4, v_l_695_);
v___x_975_ = v_reuseFailAlloc_979_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_977_; 
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 4, v___x_975_);
lean_ctor_set(v___x_962_, 3, v___x_973_);
lean_ctor_set(v___x_962_, 2, v_v_967_);
lean_ctor_set(v___x_962_, 1, v_k_966_);
lean_ctor_set(v___x_962_, 0, v___x_971_);
v___x_977_ = v___x_962_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_k_966_);
lean_ctor_set(v_reuseFailAlloc_978_, 2, v_v_967_);
lean_ctor_set(v_reuseFailAlloc_978_, 3, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_978_, 4, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
}
else
{
lean_object* v_k_991_; lean_object* v_v_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
v_k_991_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_k_991_);
v_v_992_ = lean_ctor_get(v___x_848_, 1);
lean_inc(v_v_992_);
lean_dec_ref(v___x_848_);
v___x_993_ = lean_unsigned_to_nat(2u);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 4, v_r_696_);
lean_ctor_set(v___x_846_, 3, v_l_682_);
lean_ctor_set(v___x_846_, 2, v_v_992_);
lean_ctor_set(v___x_846_, 1, v_k_991_);
lean_ctor_set(v___x_846_, 0, v___x_993_);
v___x_995_ = v___x_846_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_k_991_);
lean_ctor_set(v_reuseFailAlloc_996_, 2, v_v_992_);
lean_ctor_set(v_reuseFailAlloc_996_, 3, v_l_682_);
lean_ctor_set(v_reuseFailAlloc_996_, 4, v_r_696_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
}
}
else
{
return v_l_682_;
}
}
else
{
return v_r_683_;
}
}
else
{
lean_object* v_val_1003_; lean_object* v___x_1005_; 
v_val_1003_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_val_1003_);
lean_dec_ref_known(v___x_691_, 1);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 2, v_val_1003_);
lean_ctor_set(v___x_685_, 1, v_k_677_);
v___x_1005_ = v___x_685_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_size_679_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_k_677_);
lean_ctor_set(v_reuseFailAlloc_1006_, 2, v_val_1003_);
lean_ctor_set(v_reuseFailAlloc_1006_, 3, v_l_682_);
lean_ctor_set(v_reuseFailAlloc_1006_, 4, v_r_683_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
default: 
{
lean_object* v_impl_1007_; lean_object* v___x_1008_; 
lean_del_object(v___x_685_);
lean_dec(v_size_679_);
v_impl_1007_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_676_, v_k_677_, v_r_683_);
v___x_1008_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_680_, v_v_681_, v_l_682_, v_impl_1007_);
return v___x_1008_;
}
}
}
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_box(0);
v___x_1011_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_676_, v___x_1010_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_dec(v_k_677_);
return v_t_678_;
}
else
{
lean_object* v_val_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_val_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_val_1012_);
lean_dec_ref_known(v___x_1011_, 1);
v___x_1013_ = lean_unsigned_to_nat(1u);
v___x_1014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set(v___x_1014_, 1, v_k_677_);
lean_ctor_set(v___x_1014_, 2, v_val_1012_);
lean_ctor_set(v___x_1014_, 3, v_t_678_);
lean_ctor_set(v___x_1014_, 4, v_t_678_);
return v___x_1014_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1015_, lean_object* v_i_1016_, lean_object* v_k_1017_){
_start:
{
lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_1018_ = lean_array_get_size(v_keys_1015_);
v___x_1019_ = lean_nat_dec_lt(v_i_1016_, v___x_1018_);
if (v___x_1019_ == 0)
{
lean_dec(v_i_1016_);
return v___x_1019_;
}
else
{
lean_object* v_k_x27_1020_; uint8_t v___x_1021_; 
v_k_x27_1020_ = lean_array_fget_borrowed(v_keys_1015_, v_i_1016_);
v___x_1021_ = lean_name_eq(v_k_1017_, v_k_x27_1020_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_unsigned_to_nat(1u);
v___x_1023_ = lean_nat_add(v_i_1016_, v___x_1022_);
lean_dec(v_i_1016_);
v_i_1016_ = v___x_1023_;
goto _start;
}
else
{
lean_dec(v_i_1016_);
return v___x_1021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1025_, lean_object* v_i_1026_, lean_object* v_k_1027_){
_start:
{
uint8_t v_res_1028_; lean_object* v_r_1029_; 
v_res_1028_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_1025_, v_i_1026_, v_k_1027_);
lean_dec(v_k_1027_);
lean_dec_ref(v_keys_1025_);
v_r_1029_ = lean_box(v_res_1028_);
return v_r_1029_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(lean_object* v_x_1030_, size_t v_x_1031_, lean_object* v_x_1032_){
_start:
{
if (lean_obj_tag(v_x_1030_) == 0)
{
lean_object* v_es_1033_; lean_object* v___x_1034_; size_t v___x_1035_; size_t v___x_1036_; lean_object* v_j_1037_; lean_object* v___x_1038_; 
v_es_1033_ = lean_ctor_get(v_x_1030_, 0);
v___x_1034_ = lean_box(2);
v___x_1035_ = ((size_t)31ULL);
v___x_1036_ = lean_usize_land(v_x_1031_, v___x_1035_);
v_j_1037_ = lean_usize_to_nat(v___x_1036_);
v___x_1038_ = lean_array_get_borrowed(v___x_1034_, v_es_1033_, v_j_1037_);
lean_dec(v_j_1037_);
switch(lean_obj_tag(v___x_1038_))
{
case 0:
{
lean_object* v_key_1039_; uint8_t v___x_1040_; 
v_key_1039_ = lean_ctor_get(v___x_1038_, 0);
v___x_1040_ = lean_name_eq(v_x_1032_, v_key_1039_);
return v___x_1040_;
}
case 1:
{
lean_object* v_node_1041_; size_t v___x_1042_; size_t v___x_1043_; 
v_node_1041_ = lean_ctor_get(v___x_1038_, 0);
v___x_1042_ = ((size_t)5ULL);
v___x_1043_ = lean_usize_shift_right(v_x_1031_, v___x_1042_);
v_x_1030_ = v_node_1041_;
v_x_1031_ = v___x_1043_;
goto _start;
}
default: 
{
uint8_t v___x_1045_; 
v___x_1045_ = 0;
return v___x_1045_;
}
}
}
else
{
lean_object* v_ks_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v_ks_1046_ = lean_ctor_get(v_x_1030_, 0);
v___x_1047_ = lean_unsigned_to_nat(0u);
v___x_1048_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_ks_1046_, v___x_1047_, v_x_1032_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___boxed(lean_object* v_x_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_){
_start:
{
size_t v_x_4157__boxed_1052_; uint8_t v_res_1053_; lean_object* v_r_1054_; 
v_x_4157__boxed_1052_ = lean_unbox_usize(v_x_1050_);
lean_dec(v_x_1050_);
v_res_1053_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1049_, v_x_4157__boxed_1052_, v_x_1051_);
lean_dec(v_x_1051_);
lean_dec_ref(v_x_1049_);
v_r_1054_ = lean_box(v_res_1053_);
return v_r_1054_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(lean_object* v_x_1055_, lean_object* v_x_1056_){
_start:
{
uint64_t v___y_1058_; 
if (lean_obj_tag(v_x_1056_) == 0)
{
uint64_t v___x_1061_; 
v___x_1061_ = 1723ULL;
v___y_1058_ = v___x_1061_;
goto v___jp_1057_;
}
else
{
uint64_t v_hash_1062_; 
v_hash_1062_ = lean_ctor_get_uint64(v_x_1056_, sizeof(void*)*2);
v___y_1058_ = v_hash_1062_;
goto v___jp_1057_;
}
v___jp_1057_:
{
size_t v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = lean_uint64_to_usize(v___y_1058_);
v___x_1060_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1055_, v___x_1059_, v_x_1056_);
return v___x_1060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(lean_object* v_x_1063_, lean_object* v_x_1064_){
_start:
{
uint8_t v_res_1065_; lean_object* v_r_1066_; 
v_res_1065_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_1063_, v_x_1064_);
lean_dec(v_x_1064_);
lean_dec_ref(v_x_1063_);
v_r_1066_ = lean_box(v_res_1065_);
return v_r_1066_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(lean_object* v_tactics_1067_, lean_object* v_a_1068_, uint8_t v___x_1069_, lean_object* v_x_1070_, lean_object* v_____s_1071_){
_start:
{
lean_object* v_fst_1072_; lean_object* v_kinds_1073_; uint8_t v___x_1074_; 
v_fst_1072_ = lean_ctor_get(v_x_1070_, 0);
lean_inc(v_fst_1072_);
lean_dec_ref(v_x_1070_);
v_kinds_1073_ = lean_ctor_get(v_tactics_1067_, 1);
v___x_1074_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_kinds_1073_, v_fst_1072_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; 
lean_dec(v_fst_1072_);
lean_dec(v_a_1068_);
v___x_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1075_, 0, v_____s_1071_);
return v___x_1075_;
}
else
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1076_ = l_Lean_Name_toString(v_a_1068_, v___x_1069_);
v___x_1077_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1076_, v_fst_1072_, v_____s_1071_);
v___x_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
return v___x_1078_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(lean_object* v_tactics_1079_, lean_object* v_a_1080_, lean_object* v___x_1081_, lean_object* v_x_1082_, lean_object* v_____s_1083_){
_start:
{
uint8_t v___x_4213__boxed_1084_; lean_object* v_res_1085_; 
v___x_4213__boxed_1084_ = lean_unbox(v___x_1081_);
v_res_1085_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(v_tactics_1079_, v_a_1080_, v___x_4213__boxed_1084_, v_x_1082_, v_____s_1083_);
lean_dec_ref(v_tactics_1079_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_f_1086_, lean_object* v_keys_1087_, lean_object* v_vals_1088_, lean_object* v_i_1089_, lean_object* v_acc_1090_){
_start:
{
lean_object* v___x_1091_; uint8_t v___x_1092_; 
v___x_1091_ = lean_array_get_size(v_keys_1087_);
v___x_1092_ = lean_nat_dec_lt(v_i_1089_, v___x_1091_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; 
lean_dec(v_i_1089_);
lean_dec_ref(v_f_1086_);
v___x_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1093_, 0, v_acc_1090_);
return v___x_1093_;
}
else
{
lean_object* v_k_1094_; lean_object* v_v_1095_; lean_object* v___x_1096_; 
v_k_1094_ = lean_array_fget_borrowed(v_keys_1087_, v_i_1089_);
v_v_1095_ = lean_array_fget_borrowed(v_vals_1088_, v_i_1089_);
lean_inc_ref(v_f_1086_);
lean_inc(v_v_1095_);
lean_inc(v_k_1094_);
v___x_1096_ = lean_apply_3(v_f_1086_, v_acc_1090_, v_k_1094_, v_v_1095_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_dec(v_i_1089_);
lean_dec_ref(v_f_1086_);
return v___x_1096_;
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v___x_1096_, 1);
v___x_1098_ = lean_unsigned_to_nat(1u);
v___x_1099_ = lean_nat_add(v_i_1089_, v___x_1098_);
lean_dec(v_i_1089_);
v_i_1089_ = v___x_1099_;
v_acc_1090_ = v_a_1097_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_f_1101_, lean_object* v_keys_1102_, lean_object* v_vals_1103_, lean_object* v_i_1104_, lean_object* v_acc_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1101_, v_keys_1102_, v_vals_1103_, v_i_1104_, v_acc_1105_);
lean_dec_ref(v_vals_1103_);
lean_dec_ref(v_keys_1102_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object* v_f_1107_, lean_object* v_x_1108_, lean_object* v_x_1109_){
_start:
{
if (lean_obj_tag(v_x_1108_) == 0)
{
lean_object* v_es_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1130_; 
v_es_1110_ = lean_ctor_get(v_x_1108_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_x_1108_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1112_ = v_x_1108_;
v_isShared_1113_ = v_isSharedCheck_1130_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_es_1110_);
lean_dec(v_x_1108_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1130_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1114_ = lean_unsigned_to_nat(0u);
v___x_1115_ = lean_array_get_size(v_es_1110_);
v___x_1116_ = lean_nat_dec_lt(v___x_1114_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1118_; 
lean_dec_ref(v_es_1110_);
lean_dec_ref(v_f_1107_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set_tag(v___x_1112_, 1);
lean_ctor_set(v___x_1112_, 0, v_x_1109_);
v___x_1118_ = v___x_1112_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_x_1109_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
else
{
uint8_t v___x_1120_; 
v___x_1120_ = lean_nat_dec_le(v___x_1115_, v___x_1115_);
if (v___x_1120_ == 0)
{
if (v___x_1116_ == 0)
{
lean_object* v___x_1122_; 
lean_dec_ref(v_es_1110_);
lean_dec_ref(v_f_1107_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set_tag(v___x_1112_, 1);
lean_ctor_set(v___x_1112_, 0, v_x_1109_);
v___x_1122_ = v___x_1112_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_x_1109_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
else
{
size_t v___x_1124_; size_t v___x_1125_; lean_object* v___x_1126_; 
lean_del_object(v___x_1112_);
v___x_1124_ = ((size_t)0ULL);
v___x_1125_ = lean_usize_of_nat(v___x_1115_);
v___x_1126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1107_, v_es_1110_, v___x_1124_, v___x_1125_, v_x_1109_);
lean_dec_ref(v_es_1110_);
return v___x_1126_;
}
}
else
{
size_t v___x_1127_; size_t v___x_1128_; lean_object* v___x_1129_; 
lean_del_object(v___x_1112_);
v___x_1127_ = ((size_t)0ULL);
v___x_1128_ = lean_usize_of_nat(v___x_1115_);
v___x_1129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1107_, v_es_1110_, v___x_1127_, v___x_1128_, v_x_1109_);
lean_dec_ref(v_es_1110_);
return v___x_1129_;
}
}
}
}
else
{
lean_object* v_ks_1131_; lean_object* v_vs_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v_ks_1131_ = lean_ctor_get(v_x_1108_, 0);
lean_inc_ref(v_ks_1131_);
v_vs_1132_ = lean_ctor_get(v_x_1108_, 1);
lean_inc_ref(v_vs_1132_);
lean_dec_ref_known(v_x_1108_, 2);
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1107_, v_ks_1131_, v_vs_1132_, v___x_1133_, v_x_1109_);
lean_dec_ref(v_vs_1132_);
lean_dec_ref(v_ks_1131_);
return v___x_1134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_f_1135_, lean_object* v_as_1136_, size_t v_i_1137_, size_t v_stop_1138_, lean_object* v_b_1139_){
_start:
{
lean_object* v_a_1141_; lean_object* v___y_1146_; uint8_t v___x_1148_; 
v___x_1148_ = lean_usize_dec_eq(v_i_1137_, v_stop_1138_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_array_uget_borrowed(v_as_1136_, v_i_1137_);
switch(lean_obj_tag(v___x_1149_))
{
case 0:
{
lean_object* v_key_1150_; lean_object* v_val_1151_; lean_object* v___x_1152_; 
v_key_1150_ = lean_ctor_get(v___x_1149_, 0);
v_val_1151_ = lean_ctor_get(v___x_1149_, 1);
lean_inc_ref(v_f_1135_);
lean_inc(v_val_1151_);
lean_inc(v_key_1150_);
v___x_1152_ = lean_apply_3(v_f_1135_, v_b_1139_, v_key_1150_, v_val_1151_);
v___y_1146_ = v___x_1152_;
goto v___jp_1145_;
}
case 1:
{
lean_object* v_node_1153_; lean_object* v___x_1154_; 
v_node_1153_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_node_1153_);
lean_inc_ref(v_f_1135_);
v___x_1154_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1135_, v_node_1153_, v_b_1139_);
v___y_1146_ = v___x_1154_;
goto v___jp_1145_;
}
default: 
{
v_a_1141_ = v_b_1139_;
goto v___jp_1140_;
}
}
}
else
{
lean_object* v___x_1155_; 
lean_dec_ref(v_f_1135_);
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v_b_1139_);
return v___x_1155_;
}
v___jp_1140_:
{
size_t v___x_1142_; size_t v___x_1143_; 
v___x_1142_ = ((size_t)1ULL);
v___x_1143_ = lean_usize_add(v_i_1137_, v___x_1142_);
v_i_1137_ = v___x_1143_;
v_b_1139_ = v_a_1141_;
goto _start;
}
v___jp_1145_:
{
if (lean_obj_tag(v___y_1146_) == 0)
{
lean_dec_ref(v_f_1135_);
return v___y_1146_;
}
else
{
lean_object* v_a_1147_; 
v_a_1147_ = lean_ctor_get(v___y_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v___y_1146_, 1);
v_a_1141_ = v_a_1147_;
goto v___jp_1140_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_f_1156_, lean_object* v_as_1157_, lean_object* v_i_1158_, lean_object* v_stop_1159_, lean_object* v_b_1160_){
_start:
{
size_t v_i_boxed_1161_; size_t v_stop_boxed_1162_; lean_object* v_res_1163_; 
v_i_boxed_1161_ = lean_unbox_usize(v_i_1158_);
lean_dec(v_i_1158_);
v_stop_boxed_1162_ = lean_unbox_usize(v_stop_1159_);
lean_dec(v_stop_1159_);
v_res_1163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1156_, v_as_1157_, v_i_boxed_1161_, v_stop_boxed_1162_, v_b_1160_);
lean_dec_ref(v_as_1157_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0(lean_object* v_f_1164_, lean_object* v_s_1165_, lean_object* v_a_1166_, lean_object* v_b_1167_){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1168_, 0, v_a_1166_);
lean_ctor_set(v___x_1168_, 1, v_b_1167_);
v___x_1169_ = lean_apply_2(v_f_1164_, v___x_1168_, v_s_1165_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1169_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1169_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
v_a_1178_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1169_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1169_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(lean_object* v_map_1186_, lean_object* v_init_1187_, lean_object* v_f_1188_){
_start:
{
lean_object* v___f_1189_; lean_object* v___x_1190_; lean_object* v_a_1191_; 
v___f_1189_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1189_, 0, v_f_1188_);
lean_inc_ref(v_map_1186_);
v___x_1190_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v___f_1189_, v_map_1186_, v_init_1187_);
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1191_);
lean_dec_ref(v___x_1190_);
return v_a_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___boxed(lean_object* v_map_1192_, lean_object* v_init_1193_, lean_object* v_f_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_1192_, v_init_1193_, v_f_1194_);
lean_dec_ref(v_map_1192_);
return v_res_1195_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1196_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0);
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(lean_object* v_tactics_1199_, lean_object* v_a_1200_, uint8_t v___x_1201_, lean_object* v_as_x27_1202_, lean_object* v_b_1203_){
_start:
{
if (lean_obj_tag(v_as_x27_1202_) == 0)
{
lean_dec(v_a_1200_);
lean_dec_ref(v_tactics_1199_);
return v_b_1203_;
}
else
{
lean_object* v_head_1204_; lean_object* v_fst_1205_; lean_object* v_info_1206_; lean_object* v_tail_1207_; lean_object* v_collectKinds_1208_; lean_object* v___x_1209_; lean_object* v___f_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v_head_1204_ = lean_ctor_get(v_as_x27_1202_, 0);
v_fst_1205_ = lean_ctor_get(v_head_1204_, 0);
v_info_1206_ = lean_ctor_get(v_fst_1205_, 0);
v_tail_1207_ = lean_ctor_get(v_as_x27_1202_, 1);
v_collectKinds_1208_ = lean_ctor_get(v_info_1206_, 1);
v___x_1209_ = lean_box(v___x_1201_);
lean_inc(v_a_1200_);
lean_inc_ref(v_tactics_1199_);
v___f_1210_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1210_, 0, v_tactics_1199_);
lean_closure_set(v___f_1210_, 1, v_a_1200_);
lean_closure_set(v___f_1210_, 2, v___x_1209_);
v___x_1211_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1);
lean_inc_ref(v_collectKinds_1208_);
v___x_1212_ = lean_apply_1(v_collectKinds_1208_, v___x_1211_);
v___x_1213_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v___x_1212_, v_b_1203_, v___f_1210_);
lean_dec_ref(v___x_1212_);
v_as_x27_1202_ = v_tail_1207_;
v_b_1203_ = v___x_1213_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(lean_object* v_tactics_1215_, lean_object* v_a_1216_, lean_object* v___x_1217_, lean_object* v_as_x27_1218_, lean_object* v_b_1219_){
_start:
{
uint8_t v___x_4387__boxed_1220_; lean_object* v_res_1221_; 
v___x_4387__boxed_1220_ = lean_unbox(v___x_1217_);
v_res_1221_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1215_, v_a_1216_, v___x_4387__boxed_1220_, v_as_x27_1218_, v_b_1219_);
lean_dec(v_as_x27_1218_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(lean_object* v_tactics_1225_, lean_object* v_init_1226_, lean_object* v_x_1227_){
_start:
{
if (lean_obj_tag(v_x_1227_) == 0)
{
lean_object* v_k_1228_; lean_object* v_v_1229_; lean_object* v_l_1230_; lean_object* v_r_1231_; lean_object* v___x_1232_; lean_object* v_a_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v_k_1228_ = lean_ctor_get(v_x_1227_, 1);
lean_inc(v_k_1228_);
v_v_1229_ = lean_ctor_get(v_x_1227_, 2);
lean_inc(v_v_1229_);
v_l_1230_ = lean_ctor_get(v_x_1227_, 3);
lean_inc(v_l_1230_);
v_r_1231_ = lean_ctor_get(v_x_1227_, 4);
lean_inc(v_r_1231_);
lean_dec_ref_known(v_x_1227_, 5);
lean_inc_ref(v_tactics_1225_);
v___x_1232_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_1225_, v_init_1226_, v_l_1230_);
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
v___x_1234_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1));
v___x_1235_ = lean_name_eq(v_k_1228_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; 
lean_dec_ref(v___x_1232_);
lean_inc_ref(v_tactics_1225_);
v___x_1236_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1225_, v_k_1228_, v___x_1235_, v_v_1229_, v_a_1233_);
lean_dec(v_v_1229_);
v_init_1226_ = v___x_1236_;
v_x_1227_ = v_r_1231_;
goto _start;
}
else
{
lean_object* v_a_1238_; 
lean_dec(v_a_1233_);
lean_dec(v_v_1229_);
lean_dec(v_k_1228_);
v_a_1238_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1238_);
lean_dec_ref(v___x_1232_);
v_init_1226_ = v_a_1238_;
v_x_1227_ = v_r_1231_;
goto _start;
}
}
else
{
lean_object* v___x_1240_; 
lean_dec_ref(v_tactics_1225_);
v___x_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1240_, 0, v_init_1226_);
return v___x_1240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(lean_object* v_tactics_1241_, lean_object* v_table_1242_, lean_object* v_firsts_1243_){
_start:
{
lean_object* v___x_1244_; lean_object* v_a_1245_; 
v___x_1244_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_1241_, v_firsts_1243_, v_table_1242_);
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref(v___x_1244_);
return v_a_1245_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_object* v_00_u03b2_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_){
_start:
{
uint8_t v___x_1249_; 
v___x_1249_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_1247_, v_x_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(lean_object* v_00_u03b2_1250_, lean_object* v_x_1251_, lean_object* v_x_1252_){
_start:
{
uint8_t v_res_1253_; lean_object* v_r_1254_; 
v_res_1253_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(v_00_u03b2_1250_, v_x_1251_, v_x_1252_);
lean_dec(v_x_1252_);
lean_dec_ref(v_x_1251_);
v_r_1254_ = lean_box(v_res_1253_);
return v_r_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(lean_object* v___x_1255_, lean_object* v_k_1256_, lean_object* v_t_1257_, lean_object* v_hl_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1255_, v_k_1256_, v_t_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(lean_object* v_00_u03c3_1260_, lean_object* v_00_u03b2_1261_, lean_object* v_map_1262_, lean_object* v_init_1263_, lean_object* v_f_1264_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_1262_, v_init_1263_, v_f_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___boxed(lean_object* v_00_u03c3_1266_, lean_object* v_00_u03b2_1267_, lean_object* v_map_1268_, lean_object* v_init_1269_, lean_object* v_f_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(v_00_u03c3_1266_, v_00_u03b2_1267_, v_map_1268_, v_init_1269_, v_f_1270_);
lean_dec_ref(v_map_1268_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(lean_object* v_tactics_1272_, lean_object* v_a_1273_, uint8_t v___x_1274_, lean_object* v_as_1275_, lean_object* v_as_x27_1276_, lean_object* v_b_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1272_, v_a_1273_, v___x_1274_, v_as_x27_1276_, v_b_1277_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(lean_object* v_tactics_1280_, lean_object* v_a_1281_, lean_object* v___x_1282_, lean_object* v_as_1283_, lean_object* v_as_x27_1284_, lean_object* v_b_1285_, lean_object* v_a_1286_){
_start:
{
uint8_t v___x_4470__boxed_1287_; lean_object* v_res_1288_; 
v___x_4470__boxed_1287_ = lean_unbox(v___x_1282_);
v_res_1288_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(v_tactics_1280_, v_a_1281_, v___x_4470__boxed_1287_, v_as_1283_, v_as_x27_1284_, v_b_1285_, v_a_1286_);
lean_dec(v_as_x27_1284_);
lean_dec(v_as_1283_);
return v_res_1288_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_object* v_00_u03b2_1289_, lean_object* v_x_1290_, size_t v_x_1291_, lean_object* v_x_1292_){
_start:
{
uint8_t v___x_1293_; 
v___x_1293_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1290_, v_x_1291_, v_x_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1294_, lean_object* v_x_1295_, lean_object* v_x_1296_, lean_object* v_x_1297_){
_start:
{
size_t v_x_4479__boxed_1298_; uint8_t v_res_1299_; lean_object* v_r_1300_; 
v_x_4479__boxed_1298_ = lean_unbox_usize(v_x_1296_);
lean_dec(v_x_1296_);
v_res_1299_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(v_00_u03b2_1294_, v_x_1295_, v_x_4479__boxed_1298_, v_x_1297_);
lean_dec(v_x_1297_);
lean_dec_ref(v_x_1295_);
v_r_1300_ = lean_box(v_res_1299_);
return v_r_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(lean_object* v_map_1301_, lean_object* v_f_1302_, lean_object* v_init_1303_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1302_, v_map_1301_, v_init_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(lean_object* v_00_u03c3_1305_, lean_object* v_00_u03c3_1306_, lean_object* v_00_u03b2_1307_, lean_object* v_map_1308_, lean_object* v_f_1309_, lean_object* v_init_1310_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1309_, v_map_1308_, v_init_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1312_, lean_object* v_keys_1313_, lean_object* v_vals_1314_, lean_object* v_heq_1315_, lean_object* v_i_1316_, lean_object* v_k_1317_){
_start:
{
uint8_t v___x_1318_; 
v___x_1318_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_1313_, v_i_1316_, v_k_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1319_, lean_object* v_keys_1320_, lean_object* v_vals_1321_, lean_object* v_heq_1322_, lean_object* v_i_1323_, lean_object* v_k_1324_){
_start:
{
uint8_t v_res_1325_; lean_object* v_r_1326_; 
v_res_1325_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(v_00_u03b2_1319_, v_keys_1320_, v_vals_1321_, v_heq_1322_, v_i_1323_, v_k_1324_);
lean_dec(v_k_1324_);
lean_dec_ref(v_vals_1321_);
lean_dec_ref(v_keys_1320_);
v_r_1326_ = lean_box(v_res_1325_);
return v_r_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(lean_object* v_00_u03c3_1327_, lean_object* v_00_u03c3_1328_, lean_object* v_00_u03b1_1329_, lean_object* v_00_u03b2_1330_, lean_object* v_f_1331_, lean_object* v_x_1332_, lean_object* v_x_1333_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1331_, v_x_1332_, v_x_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b1_1335_, lean_object* v_00_u03b2_1336_, lean_object* v_00_u03c3_1337_, lean_object* v_00_u03c3_1338_, lean_object* v_f_1339_, lean_object* v_as_1340_, size_t v_i_1341_, size_t v_stop_1342_, lean_object* v_b_1343_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1339_, v_as_1340_, v_i_1341_, v_stop_1342_, v_b_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1345_, lean_object* v_00_u03b2_1346_, lean_object* v_00_u03c3_1347_, lean_object* v_00_u03c3_1348_, lean_object* v_f_1349_, lean_object* v_as_1350_, lean_object* v_i_1351_, lean_object* v_stop_1352_, lean_object* v_b_1353_){
_start:
{
size_t v_i_boxed_1354_; size_t v_stop_boxed_1355_; lean_object* v_res_1356_; 
v_i_boxed_1354_ = lean_unbox_usize(v_i_1351_);
lean_dec(v_i_1351_);
v_stop_boxed_1355_ = lean_unbox_usize(v_stop_1352_);
lean_dec(v_stop_1352_);
v_res_1356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(v_00_u03b1_1345_, v_00_u03b2_1346_, v_00_u03c3_1347_, v_00_u03c3_1348_, v_f_1349_, v_as_1350_, v_i_boxed_1354_, v_stop_boxed_1355_, v_b_1353_);
lean_dec_ref(v_as_1350_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03c3_1357_, lean_object* v_00_u03c3_1358_, lean_object* v_00_u03b1_1359_, lean_object* v_00_u03b2_1360_, lean_object* v_f_1361_, lean_object* v_keys_1362_, lean_object* v_vals_1363_, lean_object* v_heq_1364_, lean_object* v_i_1365_, lean_object* v_acc_1366_){
_start:
{
lean_object* v___x_1367_; 
v___x_1367_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1361_, v_keys_1362_, v_vals_1363_, v_i_1365_, v_acc_1366_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03c3_1368_, lean_object* v_00_u03c3_1369_, lean_object* v_00_u03b1_1370_, lean_object* v_00_u03b2_1371_, lean_object* v_f_1372_, lean_object* v_keys_1373_, lean_object* v_vals_1374_, lean_object* v_heq_1375_, lean_object* v_i_1376_, lean_object* v_acc_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(v_00_u03c3_1368_, v_00_u03c3_1369_, v_00_u03b1_1370_, v_00_u03b2_1371_, v_f_1372_, v_keys_1373_, v_vals_1374_, v_heq_1375_, v_i_1376_, v_acc_1377_);
lean_dec_ref(v_vals_1374_);
lean_dec_ref(v_keys_1373_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(lean_object* v_x1_1379_, lean_object* v_x2_1380_){
_start:
{
lean_object* v_fst_1381_; lean_object* v_snd_1382_; lean_object* v___x_1383_; 
v_fst_1381_ = lean_ctor_get(v_x2_1380_, 0);
lean_inc(v_fst_1381_);
v_snd_1382_ = lean_ctor_get(v_x2_1380_, 1);
lean_inc(v_snd_1382_);
lean_dec_ref(v_x2_1380_);
v___x_1383_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1381_, v_snd_1382_, v_x1_1379_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(lean_object* v___f_1403_, lean_object* v_x1_1404_, lean_object* v_x2_1405_){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
v___x_1406_ = lean_unsigned_to_nat(0u);
v___x_1407_ = lean_array_get_size(v_x2_1405_);
v___x_1408_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_1409_ = lean_nat_dec_lt(v___x_1406_, v___x_1407_);
if (v___x_1409_ == 0)
{
lean_dec_ref(v_x2_1405_);
lean_dec_ref(v___f_1403_);
return v_x1_1404_;
}
else
{
uint8_t v___x_1410_; 
v___x_1410_ = lean_nat_dec_le(v___x_1407_, v___x_1407_);
if (v___x_1410_ == 0)
{
if (v___x_1409_ == 0)
{
lean_dec_ref(v_x2_1405_);
lean_dec_ref(v___f_1403_);
return v_x1_1404_;
}
else
{
size_t v___x_1411_; size_t v___x_1412_; lean_object* v___x_1413_; 
v___x_1411_ = ((size_t)0ULL);
v___x_1412_ = lean_usize_of_nat(v___x_1407_);
v___x_1413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1408_, v___f_1403_, v_x2_1405_, v___x_1411_, v___x_1412_, v_x1_1404_);
return v___x_1413_;
}
}
else
{
size_t v___x_1414_; size_t v___x_1415_; lean_object* v___x_1416_; 
v___x_1414_ = ((size_t)0ULL);
v___x_1415_ = lean_usize_of_nat(v___x_1407_);
v___x_1416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1408_, v___f_1403_, v_x2_1405_, v___x_1414_, v___x_1415_, v_x1_1404_);
return v___x_1416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object* v___x_1420_, lean_object* v___x_1421_, lean_object* v___x_1422_, lean_object* v___x_1423_, lean_object* v___x_1424_, lean_object* v_toPure_1425_, lean_object* v___f_1426_, lean_object* v_env_1427_){
_start:
{
lean_object* v___x_1428_; lean_object* v_ext_1429_; lean_object* v_toEnvExtension_1430_; lean_object* v_asyncMode_1431_; lean_object* v___x_1432_; lean_object* v_categories_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1428_ = l_Lean_Parser_parserExtension;
v_ext_1429_ = lean_ctor_get(v___x_1428_, 1);
v_toEnvExtension_1430_ = lean_ctor_get(v_ext_1429_, 0);
v_asyncMode_1431_ = lean_ctor_get(v_toEnvExtension_1430_, 2);
lean_inc_ref(v_env_1427_);
v___x_1432_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1420_, v___x_1428_, v_env_1427_, v_asyncMode_1431_);
v_categories_1433_ = lean_ctor_get(v___x_1432_, 2);
lean_inc_ref(v_categories_1433_);
lean_dec(v___x_1432_);
v___x_1434_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_1435_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_1421_, v___x_1422_, v_categories_1433_, v___x_1434_);
lean_dec_ref(v_categories_1433_);
if (lean_obj_tag(v___x_1435_) == 1)
{
lean_object* v_val_1436_; lean_object* v___y_1438_; lean_object* v___x_1445_; lean_object* v_toEnvExtension_1446_; lean_object* v_exportEntriesFn_1447_; lean_object* v_asyncMode_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v_importedEntries_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v_exported_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v_val_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_val_1436_);
lean_dec_ref_known(v___x_1435_, 1);
v___x_1445_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1446_ = lean_ctor_get(v___x_1445_, 0);
v_exportEntriesFn_1447_ = lean_ctor_get(v___x_1445_, 4);
v_asyncMode_1448_ = lean_ctor_get(v_toEnvExtension_1446_, 2);
v___x_1449_ = lean_box(0);
lean_inc_ref_n(v_env_1427_, 2);
v___x_1450_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1423_, v_toEnvExtension_1446_, v_env_1427_, v_asyncMode_1448_, v___x_1449_);
v_importedEntries_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc_ref(v_importedEntries_1451_);
lean_dec(v___x_1450_);
v___x_1452_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1424_, v___x_1445_, v_env_1427_, v_asyncMode_1448_, v___x_1449_);
lean_inc_ref(v_exportEntriesFn_1447_);
v___x_1453_ = lean_apply_2(v_exportEntriesFn_1447_, v_env_1427_, v___x_1452_);
v_exported_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_exported_1454_);
lean_dec_ref(v___x_1453_);
v___x_1455_ = lean_box(1);
v___x_1456_ = lean_array_push(v_importedEntries_1451_, v_exported_1454_);
v___x_1457_ = lean_unsigned_to_nat(0u);
v___x_1458_ = lean_array_get_size(v___x_1456_);
v___x_1459_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_1460_ = lean_nat_dec_lt(v___x_1457_, v___x_1458_);
if (v___x_1460_ == 0)
{
lean_dec_ref(v___x_1456_);
lean_dec_ref(v___f_1426_);
v___y_1438_ = v___x_1455_;
goto v___jp_1437_;
}
else
{
uint8_t v___x_1461_; 
v___x_1461_ = lean_nat_dec_le(v___x_1458_, v___x_1458_);
if (v___x_1461_ == 0)
{
if (v___x_1460_ == 0)
{
lean_dec_ref(v___x_1456_);
lean_dec_ref(v___f_1426_);
v___y_1438_ = v___x_1455_;
goto v___jp_1437_;
}
else
{
size_t v___x_1462_; size_t v___x_1463_; lean_object* v___x_1464_; 
v___x_1462_ = ((size_t)0ULL);
v___x_1463_ = lean_usize_of_nat(v___x_1458_);
v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1459_, v___f_1426_, v___x_1456_, v___x_1462_, v___x_1463_, v___x_1455_);
v___y_1438_ = v___x_1464_;
goto v___jp_1437_;
}
}
else
{
size_t v___x_1465_; size_t v___x_1466_; lean_object* v___x_1467_; 
v___x_1465_ = ((size_t)0ULL);
v___x_1466_ = lean_usize_of_nat(v___x_1458_);
v___x_1467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1459_, v___f_1426_, v___x_1456_, v___x_1465_, v___x_1466_, v___x_1455_);
v___y_1438_ = v___x_1467_;
goto v___jp_1437_;
}
}
v___jp_1437_:
{
lean_object* v_tables_1439_; lean_object* v_leadingTable_1440_; lean_object* v_trailingTable_1441_; lean_object* v_firstTokens_1442_; lean_object* v_firstTokens_1443_; lean_object* v___x_1444_; 
v_tables_1439_ = lean_ctor_get(v_val_1436_, 2);
v_leadingTable_1440_ = lean_ctor_get(v_tables_1439_, 0);
v_trailingTable_1441_ = lean_ctor_get(v_tables_1439_, 2);
lean_inc(v_trailingTable_1441_);
lean_inc(v_leadingTable_1440_);
lean_inc(v_val_1436_);
v_firstTokens_1442_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_1436_, v_leadingTable_1440_, v___y_1438_);
v_firstTokens_1443_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_1436_, v_trailingTable_1441_, v_firstTokens_1442_);
v___x_1444_ = lean_apply_2(v_toPure_1425_, lean_box(0), v_firstTokens_1443_);
return v___x_1444_;
}
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_dec(v___x_1435_);
lean_dec_ref(v_env_1427_);
lean_dec_ref(v___f_1426_);
lean_dec(v___x_1424_);
v___x_1468_ = lean_box(1);
v___x_1469_ = lean_apply_2(v_toPure_1425_, lean_box(0), v___x_1468_);
return v___x_1469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed(lean_object* v___x_1470_, lean_object* v___x_1471_, lean_object* v___x_1472_, lean_object* v___x_1473_, lean_object* v___x_1474_, lean_object* v_toPure_1475_, lean_object* v___f_1476_, lean_object* v_env_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(v___x_1470_, v___x_1471_, v___x_1472_, v___x_1473_, v___x_1474_, v_toPure_1475_, v___f_1476_, v_env_1477_);
lean_dec_ref(v___x_1473_);
lean_dec_ref(v___x_1470_);
return v_res_1478_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = lean_box(1);
v___x_1483_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object* v_inst_1486_, lean_object* v_inst_1487_){
_start:
{
lean_object* v_toApplicative_1488_; lean_object* v_toBind_1489_; lean_object* v_getEnv_1490_; lean_object* v_toPure_1491_; lean_object* v___f_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___f_1498_; lean_object* v___x_1499_; 
v_toApplicative_1488_ = lean_ctor_get(v_inst_1486_, 0);
lean_inc_ref(v_toApplicative_1488_);
v_toBind_1489_ = lean_ctor_get(v_inst_1486_, 1);
lean_inc(v_toBind_1489_);
lean_dec_ref(v_inst_1486_);
v_getEnv_1490_ = lean_ctor_get(v_inst_1487_, 0);
lean_inc(v_getEnv_1490_);
lean_dec_ref(v_inst_1487_);
v_toPure_1491_ = lean_ctor_get(v_toApplicative_1488_, 1);
lean_inc(v_toPure_1491_);
lean_dec_ref(v_toApplicative_1488_);
v___f_1492_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1));
v___x_1493_ = lean_box(1);
v___x_1494_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_1495_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_1496_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___x_1497_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___f_1498_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1498_, 0, v___x_1497_);
lean_closure_set(v___f_1498_, 1, v___x_1495_);
lean_closure_set(v___f_1498_, 2, v___x_1496_);
lean_closure_set(v___f_1498_, 3, v___x_1494_);
lean_closure_set(v___f_1498_, 4, v___x_1493_);
lean_closure_set(v___f_1498_, 5, v_toPure_1491_);
lean_closure_set(v___f_1498_, 6, v___f_1492_);
v___x_1499_ = lean_apply_4(v_toBind_1489_, lean_box(0), lean_box(0), v_getEnv_1490_, v___f_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object* v_m_1500_, lean_object* v_inst_1501_, lean_object* v_inst_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(v_inst_1501_, v_inst_1502_);
return v___x_1503_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1504_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0);
v___x_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
return v___x_1506_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1507_ = lean_box(1);
v___x_1508_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4);
v___x_1509_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1);
v___x_1510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
lean_ctor_set(v___x_1510_, 1, v___x_1508_);
lean_ctor_set(v___x_1510_, 2, v___x_1507_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object* v_n_1512_, lean_object* v___y_1513_, lean_object* v_toPure_1514_, lean_object* v_firsts_1515_, lean_object* v_____do__lift_1516_){
_start:
{
lean_object* v___y_1518_; lean_object* v_val_1529_; 
if (lean_obj_tag(v_____do__lift_1516_) == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__3));
lean_inc(v_n_1512_);
v___x_1532_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_1531_, v_firsts_1515_, v_n_1512_);
if (lean_obj_tag(v___x_1532_) == 0)
{
uint8_t v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1533_ = 1;
lean_inc(v_n_1512_);
v___x_1534_ = l_Lean_Name_toString(v_n_1512_, v___x_1533_);
v___x_1535_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
v___y_1518_ = v___x_1535_;
goto v___jp_1517_;
}
else
{
lean_object* v_val_1536_; 
v_val_1536_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_val_1536_);
lean_dec_ref_known(v___x_1532_, 1);
v_val_1529_ = v_val_1536_;
goto v___jp_1528_;
}
}
else
{
lean_object* v_val_1537_; 
lean_dec(v_firsts_1515_);
v_val_1537_ = lean_ctor_get(v_____do__lift_1516_, 0);
lean_inc(v_val_1537_);
lean_dec_ref_known(v_____do__lift_1516_, 1);
v_val_1529_ = v_val_1537_;
goto v___jp_1528_;
}
v___jp_1517_:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1519_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_1520_ = l_Lean_Expr_const___override(v_n_1512_, v___y_1513_);
v___x_1521_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2);
v___x_1522_ = lean_box(0);
v___x_1523_ = 0;
v___x_1524_ = l_Lean_MessageData_withExprHover(v___y_1518_, v___x_1520_, v___x_1521_, v___x_1522_, v___x_1522_, v___x_1522_, v___x_1523_);
v___x_1525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1519_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
v___x_1526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v___x_1519_);
v___x_1527_ = lean_apply_2(v_toPure_1514_, lean_box(0), v___x_1526_);
return v___x_1527_;
}
v___jp_1528_:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1530_, 0, v_val_1529_);
v___y_1518_ = v___x_1530_;
goto v___jp_1517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object* v_n_1538_, lean_object* v_toPure_1539_, lean_object* v_firsts_1540_, lean_object* v_inst_1541_, lean_object* v_inst_1542_, lean_object* v_toBind_1543_, lean_object* v___x_1544_, lean_object* v___x_1545_, lean_object* v___f_1546_, lean_object* v_env_1547_){
_start:
{
lean_object* v___y_1549_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = l_Lean_Environment_constants(v_env_1547_);
lean_inc(v_n_1538_);
v___x_1554_ = l_Lean_SMap_find_x3f_x27___redArg(v___x_1544_, v___x_1545_, v___x_1553_, v_n_1538_);
lean_dec_ref(v___x_1553_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v___x_1555_; 
lean_dec_ref(v___f_1546_);
v___x_1555_ = lean_box(0);
v___y_1549_ = v___x_1555_;
goto v___jp_1548_;
}
else
{
lean_object* v_val_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v_val_1556_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_val_1556_);
lean_dec_ref_known(v___x_1554_, 1);
v___x_1557_ = l_Lean_ConstantInfo_levelParams(v_val_1556_);
lean_dec(v_val_1556_);
v___x_1558_ = lean_box(0);
v___x_1559_ = l_List_mapTR_loop___redArg(v___f_1546_, v___x_1557_, v___x_1558_);
v___y_1549_ = v___x_1559_;
goto v___jp_1548_;
}
v___jp_1548_:
{
lean_object* v___f_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
lean_inc(v_n_1538_);
v___f_1550_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1550_, 0, v_n_1538_);
lean_closure_set(v___f_1550_, 1, v___y_1549_);
lean_closure_set(v___f_1550_, 2, v_toPure_1539_);
lean_closure_set(v___f_1550_, 3, v_firsts_1540_);
v___x_1551_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(v_inst_1541_, v_inst_1542_, v_n_1538_);
v___x_1552_ = lean_apply_4(v_toBind_1543_, lean_box(0), lean_box(0), v___x_1551_, v___f_1550_);
return v___x_1552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object* v_inst_1561_, lean_object* v_inst_1562_, lean_object* v_firsts_1563_, lean_object* v_n_1564_){
_start:
{
lean_object* v_toApplicative_1565_; lean_object* v_toBind_1566_; lean_object* v_getEnv_1567_; lean_object* v_toPure_1568_; lean_object* v___f_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___f_1572_; lean_object* v___x_1573_; 
v_toApplicative_1565_ = lean_ctor_get(v_inst_1561_, 0);
v_toBind_1566_ = lean_ctor_get(v_inst_1561_, 1);
lean_inc_n(v_toBind_1566_, 2);
v_getEnv_1567_ = lean_ctor_get(v_inst_1562_, 0);
lean_inc(v_getEnv_1567_);
v_toPure_1568_ = lean_ctor_get(v_toApplicative_1565_, 1);
lean_inc(v_toPure_1568_);
v___f_1569_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0));
v___x_1570_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_1571_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___f_1572_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1572_, 0, v_n_1564_);
lean_closure_set(v___f_1572_, 1, v_toPure_1568_);
lean_closure_set(v___f_1572_, 2, v_firsts_1563_);
lean_closure_set(v___f_1572_, 3, v_inst_1561_);
lean_closure_set(v___f_1572_, 4, v_inst_1562_);
lean_closure_set(v___f_1572_, 5, v_toBind_1566_);
lean_closure_set(v___f_1572_, 6, v___x_1570_);
lean_closure_set(v___f_1572_, 7, v___x_1571_);
lean_closure_set(v___f_1572_, 8, v___f_1569_);
v___x_1573_ = lean_apply_4(v_toBind_1566_, lean_box(0), lean_box(0), v_getEnv_1567_, v___f_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object* v_m_1574_, lean_object* v_inst_1575_, lean_object* v_inst_1576_, lean_object* v_firsts_1577_, lean_object* v_n_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(v_inst_1575_, v_inst_1576_, v_firsts_1577_, v_n_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object* v_s_1582_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0));
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object* v_s_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v_s_1584_);
lean_dec_ref(v_s_1584_);
return v_res_1585_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t v___x_1586_, lean_object* v_x1_1587_, lean_object* v_x2_1588_){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; uint8_t v___x_1591_; 
v___x_1589_ = l_Lean_Name_toString(v_x1_1587_, v___x_1586_);
v___x_1590_ = l_Lean_Name_toString(v_x2_1588_, v___x_1586_);
v___x_1591_ = lean_string_dec_lt(v___x_1589_, v___x_1590_);
lean_dec_ref(v___x_1590_);
lean_dec_ref(v___x_1589_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object* v___x_1592_, lean_object* v_x1_1593_, lean_object* v_x2_1594_){
_start:
{
uint8_t v___x_17215__boxed_1595_; uint8_t v_res_1596_; lean_object* v_r_1597_; 
v___x_17215__boxed_1595_ = lean_unbox(v___x_1592_);
v_res_1596_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_17215__boxed_1595_, v_x1_1593_, v_x2_1594_);
v_r_1597_ = lean_box(v_res_1596_);
return v_r_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(lean_object* v_hi_1598_, lean_object* v_pivot_1599_, lean_object* v_as_1600_, lean_object* v_i_1601_, lean_object* v_k_1602_){
_start:
{
uint8_t v___x_1603_; 
v___x_1603_ = lean_nat_dec_lt(v_k_1602_, v_hi_1598_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
lean_dec(v_k_1602_);
lean_dec(v_pivot_1599_);
v___x_1604_ = lean_array_fswap(v_as_1600_, v_i_1601_, v_hi_1598_);
v___x_1605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1605_, 0, v_i_1601_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
return v___x_1605_;
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; 
v___x_1606_ = lean_array_fget_borrowed(v_as_1600_, v_k_1602_);
lean_inc(v___x_1606_);
v___x_1607_ = l_Lean_Name_toString(v___x_1606_, v___x_1603_);
lean_inc(v_pivot_1599_);
v___x_1608_ = l_Lean_Name_toString(v_pivot_1599_, v___x_1603_);
v___x_1609_ = lean_string_dec_lt(v___x_1607_, v___x_1608_);
lean_dec_ref(v___x_1608_);
lean_dec_ref(v___x_1607_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = lean_unsigned_to_nat(1u);
v___x_1611_ = lean_nat_add(v_k_1602_, v___x_1610_);
lean_dec(v_k_1602_);
v_k_1602_ = v___x_1611_;
goto _start;
}
else
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1613_ = lean_array_fswap(v_as_1600_, v_i_1601_, v_k_1602_);
v___x_1614_ = lean_unsigned_to_nat(1u);
v___x_1615_ = lean_nat_add(v_i_1601_, v___x_1614_);
lean_dec(v_i_1601_);
v___x_1616_ = lean_nat_add(v_k_1602_, v___x_1614_);
lean_dec(v_k_1602_);
v_as_1600_ = v___x_1613_;
v_i_1601_ = v___x_1615_;
v_k_1602_ = v___x_1616_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg___boxed(lean_object* v_hi_1618_, lean_object* v_pivot_1619_, lean_object* v_as_1620_, lean_object* v_i_1621_, lean_object* v_k_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_1618_, v_pivot_1619_, v_as_1620_, v_i_1621_, v_k_1622_);
lean_dec(v_hi_1618_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object* v_n_1624_, lean_object* v_as_1625_, lean_object* v_lo_1626_, lean_object* v_hi_1627_){
_start:
{
lean_object* v___y_1629_; uint8_t v___x_1639_; 
v___x_1639_ = lean_nat_dec_lt(v_lo_1626_, v_hi_1627_);
if (v___x_1639_ == 0)
{
lean_dec(v_lo_1626_);
return v_as_1625_;
}
else
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v_mid_1642_; lean_object* v___y_1644_; lean_object* v___y_1650_; lean_object* v___x_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; 
v___x_1640_ = lean_nat_add(v_lo_1626_, v_hi_1627_);
v___x_1641_ = lean_unsigned_to_nat(1u);
v_mid_1642_ = lean_nat_shiftr(v___x_1640_, v___x_1641_);
lean_dec(v___x_1640_);
v___x_1655_ = lean_array_fget_borrowed(v_as_1625_, v_mid_1642_);
v___x_1656_ = lean_array_fget_borrowed(v_as_1625_, v_lo_1626_);
lean_inc(v___x_1656_);
lean_inc(v___x_1655_);
v___x_1657_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1639_, v___x_1655_, v___x_1656_);
if (v___x_1657_ == 0)
{
v___y_1650_ = v_as_1625_;
goto v___jp_1649_;
}
else
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_array_fswap(v_as_1625_, v_lo_1626_, v_mid_1642_);
v___y_1650_ = v___x_1658_;
goto v___jp_1649_;
}
v___jp_1643_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1645_ = lean_array_fget_borrowed(v___y_1644_, v_mid_1642_);
v___x_1646_ = lean_array_fget_borrowed(v___y_1644_, v_hi_1627_);
lean_inc(v___x_1646_);
lean_inc(v___x_1645_);
v___x_1647_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1639_, v___x_1645_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_dec(v_mid_1642_);
v___y_1629_ = v___y_1644_;
goto v___jp_1628_;
}
else
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_array_fswap(v___y_1644_, v_mid_1642_, v_hi_1627_);
lean_dec(v_mid_1642_);
v___y_1629_ = v___x_1648_;
goto v___jp_1628_;
}
}
v___jp_1649_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v___x_1651_ = lean_array_fget_borrowed(v___y_1650_, v_hi_1627_);
v___x_1652_ = lean_array_fget_borrowed(v___y_1650_, v_lo_1626_);
lean_inc(v___x_1652_);
lean_inc(v___x_1651_);
v___x_1653_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1639_, v___x_1651_, v___x_1652_);
if (v___x_1653_ == 0)
{
v___y_1644_ = v___y_1650_;
goto v___jp_1643_;
}
else
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_array_fswap(v___y_1650_, v_lo_1626_, v_hi_1627_);
v___y_1644_ = v___x_1654_;
goto v___jp_1643_;
}
}
}
v___jp_1628_:
{
lean_object* v_pivot_1630_; lean_object* v___x_1631_; lean_object* v_fst_1632_; lean_object* v_snd_1633_; uint8_t v___x_1634_; 
v_pivot_1630_ = lean_array_fget(v___y_1629_, v_hi_1627_);
lean_inc_n(v_lo_1626_, 2);
v___x_1631_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_1627_, v_pivot_1630_, v___y_1629_, v_lo_1626_, v_lo_1626_);
v_fst_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_fst_1632_);
v_snd_1633_ = lean_ctor_get(v___x_1631_, 1);
lean_inc(v_snd_1633_);
lean_dec_ref(v___x_1631_);
v___x_1634_ = lean_nat_dec_le(v_hi_1627_, v_fst_1632_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1635_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_1624_, v_snd_1633_, v_lo_1626_, v_fst_1632_);
v___x_1636_ = lean_unsigned_to_nat(1u);
v___x_1637_ = lean_nat_add(v_fst_1632_, v___x_1636_);
lean_dec(v_fst_1632_);
v_as_1625_ = v___x_1635_;
v_lo_1626_ = v___x_1637_;
goto _start;
}
else
{
lean_dec(v_fst_1632_);
lean_dec(v_lo_1626_);
return v_snd_1633_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object* v_n_1659_, lean_object* v_as_1660_, lean_object* v_lo_1661_, lean_object* v_hi_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_1659_, v_as_1660_, v_lo_1661_, v_hi_1662_);
lean_dec(v_hi_1662_);
lean_dec(v_n_1659_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(lean_object* v_init_1664_, lean_object* v_x_1665_){
_start:
{
if (lean_obj_tag(v_x_1665_) == 0)
{
lean_object* v_k_1666_; lean_object* v_l_1667_; lean_object* v_r_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v_k_1666_ = lean_ctor_get(v_x_1665_, 1);
lean_inc(v_k_1666_);
v_l_1667_ = lean_ctor_get(v_x_1665_, 3);
lean_inc(v_l_1667_);
v_r_1668_ = lean_ctor_get(v_x_1665_, 4);
lean_inc(v_r_1668_);
lean_dec_ref_known(v_x_1665_, 5);
v___x_1669_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_1664_, v_l_1667_);
v___x_1670_ = lean_array_push(v___x_1669_, v_k_1666_);
v_init_1664_ = v___x_1670_;
v_x_1665_ = v_r_1668_;
goto _start;
}
else
{
return v_init_1664_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object* v_a_1672_, lean_object* v_a_1673_){
_start:
{
if (lean_obj_tag(v_a_1672_) == 0)
{
lean_object* v___x_1674_; 
v___x_1674_ = l_List_reverse___redArg(v_a_1673_);
return v___x_1674_;
}
else
{
lean_object* v_head_1675_; lean_object* v_tail_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1685_; 
v_head_1675_ = lean_ctor_get(v_a_1672_, 0);
v_tail_1676_ = lean_ctor_get(v_a_1672_, 1);
v_isSharedCheck_1685_ = !lean_is_exclusive(v_a_1672_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1678_ = v_a_1672_;
v_isShared_1679_ = v_isSharedCheck_1685_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_tail_1676_);
lean_inc(v_head_1675_);
lean_dec(v_a_1672_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1685_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1680_ = l_Lean_Level_param___override(v_head_1675_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 1, v_a_1673_);
lean_ctor_set(v___x_1678_, 0, v___x_1680_);
v___x_1682_ = v___x_1678_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1680_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_a_1673_);
v___x_1682_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
v_a_1672_ = v_tail_1676_;
v_a_1673_ = v___x_1682_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object* v_x1_1686_, lean_object* v_x2_1687_){
_start:
{
lean_object* v_fst_1688_; lean_object* v_fst_1689_; uint8_t v___x_1690_; 
v_fst_1688_ = lean_ctor_get(v_x1_1686_, 0);
v_fst_1689_ = lean_ctor_get(v_x2_1687_, 0);
v___x_1690_ = l_Lean_Name_quickLt(v_fst_1688_, v_fst_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_x1_1691_, lean_object* v_x2_1692_){
_start:
{
uint8_t v_res_1693_; lean_object* v_r_1694_; 
v_res_1693_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_x1_1691_, v_x2_1692_);
lean_dec_ref(v_x2_1692_);
lean_dec_ref(v_x1_1691_);
v_r_1694_ = lean_box(v_res_1693_);
return v_r_1694_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object* v_as_1695_, lean_object* v_k_1696_, lean_object* v_x_1697_, lean_object* v_x_1698_){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v_m_1701_; lean_object* v_a_1702_; uint8_t v___x_1703_; 
v___x_1699_ = lean_nat_add(v_x_1697_, v_x_1698_);
v___x_1700_ = lean_unsigned_to_nat(1u);
v_m_1701_ = lean_nat_shiftr(v___x_1699_, v___x_1700_);
lean_dec(v___x_1699_);
v_a_1702_ = lean_array_fget_borrowed(v_as_1695_, v_m_1701_);
v___x_1703_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_a_1702_, v_k_1696_);
if (v___x_1703_ == 0)
{
uint8_t v___x_1704_; 
lean_dec(v_x_1698_);
v___x_1704_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_k_1696_, v_a_1702_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; 
lean_dec(v_m_1701_);
lean_dec(v_x_1697_);
lean_inc(v_a_1702_);
v___x_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1705_, 0, v_a_1702_);
return v___x_1705_;
}
else
{
lean_object* v___x_1706_; uint8_t v___x_1707_; 
v___x_1706_ = lean_unsigned_to_nat(0u);
v___x_1707_ = lean_nat_dec_eq(v_m_1701_, v___x_1706_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1708_ = lean_nat_sub(v_m_1701_, v___x_1700_);
lean_dec(v_m_1701_);
v___x_1709_ = lean_nat_dec_lt(v___x_1708_, v_x_1697_);
if (v___x_1709_ == 0)
{
v_x_1698_ = v___x_1708_;
goto _start;
}
else
{
lean_object* v___x_1711_; 
lean_dec(v___x_1708_);
lean_dec(v_x_1697_);
v___x_1711_ = lean_box(0);
return v___x_1711_;
}
}
else
{
lean_object* v___x_1712_; 
lean_dec(v_m_1701_);
lean_dec(v_x_1697_);
v___x_1712_ = lean_box(0);
return v___x_1712_;
}
}
}
else
{
lean_object* v___x_1713_; uint8_t v___x_1714_; 
lean_dec(v_x_1697_);
v___x_1713_ = lean_nat_add(v_m_1701_, v___x_1700_);
lean_dec(v_m_1701_);
v___x_1714_ = lean_nat_dec_le(v___x_1713_, v_x_1698_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; 
lean_dec(v___x_1713_);
lean_dec(v_x_1698_);
v___x_1715_ = lean_box(0);
return v___x_1715_;
}
else
{
v_x_1697_ = v___x_1713_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_as_1717_, lean_object* v_k_1718_, lean_object* v_x_1719_, lean_object* v_x_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_1717_, v_k_1718_, v_x_1719_, v_x_1720_);
lean_dec_ref(v_k_1718_);
lean_dec_ref(v_as_1717_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object* v_tac_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v___x_1726_; lean_object* v_env_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1726_ = lean_st_ref_get(v___y_1724_);
v_env_1730_ = lean_ctor_get(v___x_1726_, 0);
lean_inc_ref(v_env_1730_);
lean_dec(v___x_1726_);
v___x_1731_ = lean_box(1);
v___x_1732_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1730_, v_tac_1723_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v___x_1733_; lean_object* v_toEnvExtension_1734_; lean_object* v_asyncMode_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1733_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1734_ = lean_ctor_get(v___x_1733_, 0);
v_asyncMode_1735_ = lean_ctor_get(v_toEnvExtension_1734_, 2);
v___x_1736_ = lean_box(0);
v___x_1737_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1731_, v___x_1733_, v_env_1730_, v_asyncMode_1735_, v___x_1736_);
v___x_1738_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1737_, v_tac_1723_);
lean_dec(v_tac_1723_);
lean_dec(v___x_1737_);
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
return v___x_1739_;
}
else
{
lean_object* v_val_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1768_; 
v_val_1740_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1742_ = v___x_1732_;
v_isShared_1743_ = v_isSharedCheck_1768_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_val_1740_);
lean_dec(v___x_1732_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1768_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; uint8_t v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v___x_1744_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_1745_ = 0;
v___x_1746_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1731_, v___x_1744_, v_env_1730_, v_val_1740_, v___x_1745_);
lean_dec(v_val_1740_);
lean_dec_ref(v_env_1730_);
v___x_1747_ = lean_unsigned_to_nat(0u);
v___x_1748_ = lean_array_get_size(v___x_1746_);
v___x_1749_ = lean_nat_dec_lt(v___x_1747_, v___x_1748_);
if (v___x_1749_ == 0)
{
lean_dec_ref(v___x_1746_);
lean_del_object(v___x_1742_);
lean_dec(v_tac_1723_);
goto v___jp_1727_;
}
else
{
lean_object* v___x_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; 
v___x_1750_ = lean_unsigned_to_nat(1u);
v___x_1751_ = lean_nat_sub(v___x_1748_, v___x_1750_);
v___x_1752_ = lean_nat_dec_le(v___x_1747_, v___x_1751_);
if (v___x_1752_ == 0)
{
lean_dec(v___x_1751_);
lean_dec_ref(v___x_1746_);
lean_del_object(v___x_1742_);
lean_dec(v_tac_1723_);
goto v___jp_1727_;
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1753_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
v___x_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1754_, 0, v_tac_1723_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
v___x_1755_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v___x_1746_, v___x_1754_, v___x_1747_, v___x_1751_);
lean_dec_ref_known(v___x_1754_, 2);
lean_dec_ref(v___x_1746_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_del_object(v___x_1742_);
goto v___jp_1727_;
}
else
{
lean_object* v_val_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1767_; 
v_val_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1767_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_val_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1767_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v_snd_1760_; lean_object* v___x_1762_; 
v_snd_1760_ = lean_ctor_get(v_val_1756_, 1);
lean_inc(v_snd_1760_);
lean_dec(v_val_1756_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v_snd_1760_);
v___x_1762_ = v___x_1758_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_snd_1760_);
v___x_1762_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
lean_object* v___x_1764_; 
if (v_isShared_1743_ == 0)
{
lean_ctor_set_tag(v___x_1742_, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1762_);
v___x_1764_ = v___x_1742_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
}
}
}
}
v___jp_1727_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = lean_box(0);
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
return v___x_1729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object* v_tac_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_1769_, v___y_1770_);
lean_dec(v___y_1770_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object* v_t_1773_, lean_object* v_k_1774_){
_start:
{
if (lean_obj_tag(v_t_1773_) == 0)
{
lean_object* v_k_1775_; lean_object* v_v_1776_; lean_object* v_l_1777_; lean_object* v_r_1778_; uint8_t v___x_1779_; 
v_k_1775_ = lean_ctor_get(v_t_1773_, 1);
v_v_1776_ = lean_ctor_get(v_t_1773_, 2);
v_l_1777_ = lean_ctor_get(v_t_1773_, 3);
v_r_1778_ = lean_ctor_get(v_t_1773_, 4);
v___x_1779_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1774_, v_k_1775_);
switch(v___x_1779_)
{
case 0:
{
v_t_1773_ = v_l_1777_;
goto _start;
}
case 1:
{
lean_object* v___x_1781_; 
lean_inc(v_v_1776_);
v___x_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1781_, 0, v_v_1776_);
return v___x_1781_;
}
default: 
{
v_t_1773_ = v_r_1778_;
goto _start;
}
}
}
else
{
lean_object* v___x_1783_; 
v___x_1783_ = lean_box(0);
return v___x_1783_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg___boxed(lean_object* v_t_1784_, lean_object* v_k_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_1784_, v_k_1785_);
lean_dec(v_k_1785_);
lean_dec(v_t_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32_spec__36___redArg(lean_object* v_m_1787_, lean_object* v_query_1788_, lean_object* v_x_1789_, lean_object* v_x_1790_, lean_object* v_x_1791_){
_start:
{
lean_object* v_zero_1792_; uint8_t v_isZero_1793_; 
v_zero_1792_ = lean_unsigned_to_nat(0u);
v_isZero_1793_ = lean_nat_dec_eq(v_x_1790_, v_zero_1792_);
if (v_isZero_1793_ == 1)
{
lean_dec(v_x_1791_);
lean_dec(v_x_1790_);
if (lean_obj_tag(v_x_1789_) == 0)
{
lean_object* v___x_1794_; 
v___x_1794_ = lean_box(2);
return v___x_1794_;
}
else
{
lean_object* v_val_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
v_val_1795_ = lean_ctor_get(v_x_1789_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_x_1789_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v_x_1789_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_val_1795_);
lean_dec(v_x_1789_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_val_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
else
{
lean_object* v_keyArray_1803_; lean_object* v_valueArray_1804_; lean_object* v___x_1805_; uint8_t v_isSome_1806_; 
v_keyArray_1803_ = lean_ctor_get(v_m_1787_, 1);
v_valueArray_1804_ = lean_ctor_get(v_m_1787_, 2);
v___x_1805_ = lean_array_fget_borrowed(v_keyArray_1803_, v_x_1791_);
v_isSome_1806_ = lean_noption_is_some(v___x_1805_);
if (v_isSome_1806_ == 0)
{
lean_dec(v_x_1790_);
if (lean_obj_tag(v_x_1789_) == 0)
{
lean_object* v___x_1807_; 
v___x_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1807_, 0, v_x_1791_);
return v___x_1807_;
}
else
{
lean_object* v_val_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
lean_dec(v_x_1791_);
v_val_1808_ = lean_ctor_get(v_x_1789_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_x_1789_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v_x_1789_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_val_1808_);
lean_dec(v_x_1789_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_val_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
else
{
lean_object* v_one_1816_; lean_object* v_n_1817_; lean_object* v___y_1819_; 
v_one_1816_ = lean_unsigned_to_nat(1u);
v_n_1817_ = lean_nat_sub(v_x_1790_, v_one_1816_);
lean_dec(v_x_1790_);
if (v_isSome_1806_ == 0)
{
goto v___jp_1825_;
}
else
{
lean_object* v___x_1827_; uint8_t v_isSome_1828_; 
v___x_1827_ = lean_array_fget_borrowed(v_valueArray_1804_, v_x_1791_);
v_isSome_1828_ = lean_noption_is_some(v___x_1827_);
if (v_isSome_1828_ == 0)
{
goto v___jp_1825_;
}
else
{
lean_object* v_val_1829_; uint8_t v___x_1830_; 
lean_inc(v___x_1805_);
v_val_1829_ = lean_noption_get(v___x_1805_);
v___x_1830_ = lean_name_eq(v_val_1829_, v_query_1788_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
lean_dec(v_val_1829_);
v___x_1831_ = lean_array_get_size(v_keyArray_1803_);
v___x_1832_ = lean_nat_add(v_x_1791_, v_one_1816_);
lean_dec(v_x_1791_);
v___x_1833_ = lean_nat_dec_lt(v___x_1832_, v___x_1831_);
if (v___x_1833_ == 0)
{
lean_dec(v___x_1832_);
v_x_1790_ = v_n_1817_;
v_x_1791_ = v_zero_1792_;
goto _start;
}
else
{
v_x_1790_ = v_n_1817_;
v_x_1791_ = v___x_1832_;
goto _start;
}
}
else
{
lean_object* v_val_1836_; lean_object* v___x_1837_; 
lean_dec(v_n_1817_);
lean_dec(v_x_1789_);
lean_inc(v___x_1827_);
v_val_1836_ = lean_noption_get(v___x_1827_);
v___x_1837_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1837_, 0, v_x_1791_);
lean_ctor_set(v___x_1837_, 1, v_val_1829_);
lean_ctor_set(v___x_1837_, 2, v_val_1836_);
return v___x_1837_;
}
}
}
v___jp_1818_:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; uint8_t v___x_1822_; 
v___x_1820_ = lean_array_get_size(v_keyArray_1803_);
v___x_1821_ = lean_nat_add(v_x_1791_, v_one_1816_);
lean_dec(v_x_1791_);
v___x_1822_ = lean_nat_dec_lt(v___x_1821_, v___x_1820_);
if (v___x_1822_ == 0)
{
lean_dec(v___x_1821_);
v_x_1789_ = v___y_1819_;
v_x_1790_ = v_n_1817_;
v_x_1791_ = v_zero_1792_;
goto _start;
}
else
{
v_x_1789_ = v___y_1819_;
v_x_1790_ = v_n_1817_;
v_x_1791_ = v___x_1821_;
goto _start;
}
}
v___jp_1825_:
{
if (lean_obj_tag(v_x_1789_) == 0)
{
lean_object* v___x_1826_; 
lean_inc(v_x_1791_);
v___x_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1826_, 0, v_x_1791_);
v___y_1819_ = v___x_1826_;
goto v___jp_1818_;
}
else
{
v___y_1819_ = v_x_1789_;
goto v___jp_1818_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32_spec__36___redArg___boxed(lean_object* v_m_1838_, lean_object* v_query_1839_, lean_object* v_x_1840_, lean_object* v_x_1841_, lean_object* v_x_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32_spec__36___redArg(v_m_1838_, v_query_1839_, v_x_1840_, v_x_1841_, v_x_1842_);
lean_dec(v_query_1839_);
lean_dec_ref(v_m_1838_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32___redArg(lean_object* v_m_1844_, lean_object* v_query_1845_){
_start:
{
lean_object* v_keyArray_1846_; lean_object* v___x_1847_; uint64_t v___y_1849_; 
v_keyArray_1846_ = lean_ctor_get(v_m_1844_, 1);
v___x_1847_ = lean_array_get_size(v_keyArray_1846_);
if (lean_obj_tag(v_query_1845_) == 0)
{
uint64_t v___x_1864_; 
v___x_1864_ = 1723ULL;
v___y_1849_ = v___x_1864_;
goto v___jp_1848_;
}
else
{
uint64_t v_hash_1865_; 
v_hash_1865_ = lean_ctor_get_uint64(v_query_1845_, sizeof(void*)*2);
v___y_1849_ = v_hash_1865_;
goto v___jp_1848_;
}
v___jp_1848_:
{
uint64_t v___x_1850_; uint64_t v___x_1851_; uint64_t v_fold_1852_; uint64_t v___x_1853_; uint64_t v___x_1854_; uint64_t v___x_1855_; size_t v___x_1856_; size_t v___x_1857_; size_t v___x_1858_; size_t v___x_1859_; size_t v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1850_ = 32ULL;
v___x_1851_ = lean_uint64_shift_right(v___y_1849_, v___x_1850_);
v_fold_1852_ = lean_uint64_xor(v___y_1849_, v___x_1851_);
v___x_1853_ = 16ULL;
v___x_1854_ = lean_uint64_shift_right(v_fold_1852_, v___x_1853_);
v___x_1855_ = lean_uint64_xor(v_fold_1852_, v___x_1854_);
v___x_1856_ = lean_uint64_to_usize(v___x_1855_);
v___x_1857_ = lean_usize_of_nat(v___x_1847_);
v___x_1858_ = ((size_t)1ULL);
v___x_1859_ = lean_usize_sub(v___x_1857_, v___x_1858_);
v___x_1860_ = lean_usize_land(v___x_1856_, v___x_1859_);
v___x_1861_ = lean_usize_to_nat(v___x_1860_);
v___x_1862_ = lean_box(0);
v___x_1863_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32_spec__36___redArg(v_m_1844_, v_query_1845_, v___x_1862_, v___x_1847_, v___x_1861_);
return v___x_1863_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32___redArg___boxed(lean_object* v_m_1866_, lean_object* v_query_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32___redArg(v_m_1866_, v_query_1867_);
lean_dec(v_query_1867_);
lean_dec_ref(v_m_1866_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(lean_object* v_m_1869_, lean_object* v_query_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32___redArg(v_m_1869_, v_query_1870_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_index_1872_; lean_object* v_key_1873_; lean_object* v_value_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
v_index_1872_ = lean_ctor_get(v___x_1871_, 0);
v_key_1873_ = lean_ctor_get(v___x_1871_, 1);
v_value_1874_ = lean_ctor_get(v___x_1871_, 2);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1871_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_value_1874_);
lean_inc(v_key_1873_);
lean_inc(v_index_1872_);
lean_dec(v___x_1871_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_index_1872_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_key_1873_);
lean_ctor_set(v_reuseFailAlloc_1880_, 2, v_value_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
else
{
lean_object* v___x_1882_; 
lean_dec(v___x_1871_);
v___x_1882_ = lean_box(1);
return v___x_1882_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg___boxed(lean_object* v_m_1883_, lean_object* v_query_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_m_1883_, v_query_1884_);
lean_dec(v_query_1884_);
lean_dec_ref(v_m_1883_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(lean_object* v_m_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_m_1886_, v_a_1887_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_value_1889_; lean_object* v___x_1890_; 
v_value_1889_ = lean_ctor_get(v___x_1888_, 2);
lean_inc(v_value_1889_);
lean_dec_ref_known(v___x_1888_, 3);
v___x_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1890_, 0, v_value_1889_);
return v___x_1890_;
}
else
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_box(0);
return v___x_1891_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg___boxed(lean_object* v_m_1892_, lean_object* v_a_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_1892_, v_a_1893_);
lean_dec(v_a_1893_);
lean_dec_ref(v_m_1892_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_keys_1895_, lean_object* v_vals_1896_, lean_object* v_i_1897_, lean_object* v_k_1898_){
_start:
{
lean_object* v___x_1899_; uint8_t v___x_1900_; 
v___x_1899_ = lean_array_get_size(v_keys_1895_);
v___x_1900_ = lean_nat_dec_lt(v_i_1897_, v___x_1899_);
if (v___x_1900_ == 0)
{
lean_object* v___x_1901_; 
lean_dec(v_i_1897_);
v___x_1901_ = lean_box(0);
return v___x_1901_;
}
else
{
lean_object* v_k_x27_1902_; uint8_t v___x_1903_; 
v_k_x27_1902_ = lean_array_fget_borrowed(v_keys_1895_, v_i_1897_);
v___x_1903_ = lean_name_eq(v_k_1898_, v_k_x27_1902_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = lean_unsigned_to_nat(1u);
v___x_1905_ = lean_nat_add(v_i_1897_, v___x_1904_);
lean_dec(v_i_1897_);
v_i_1897_ = v___x_1905_;
goto _start;
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = lean_array_fget_borrowed(v_vals_1896_, v_i_1897_);
lean_dec(v_i_1897_);
lean_inc(v___x_1907_);
v___x_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
return v___x_1908_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object* v_keys_1909_, lean_object* v_vals_1910_, lean_object* v_i_1911_, lean_object* v_k_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_1909_, v_vals_1910_, v_i_1911_, v_k_1912_);
lean_dec(v_k_1912_);
lean_dec_ref(v_vals_1910_);
lean_dec_ref(v_keys_1909_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object* v_x_1914_, size_t v_x_1915_, lean_object* v_x_1916_){
_start:
{
if (lean_obj_tag(v_x_1914_) == 0)
{
lean_object* v_es_1917_; lean_object* v___x_1918_; size_t v___x_1919_; size_t v___x_1920_; lean_object* v_j_1921_; lean_object* v___x_1922_; 
v_es_1917_ = lean_ctor_get(v_x_1914_, 0);
v___x_1918_ = lean_box(2);
v___x_1919_ = ((size_t)31ULL);
v___x_1920_ = lean_usize_land(v_x_1915_, v___x_1919_);
v_j_1921_ = lean_usize_to_nat(v___x_1920_);
v___x_1922_ = lean_array_get_borrowed(v___x_1918_, v_es_1917_, v_j_1921_);
lean_dec(v_j_1921_);
switch(lean_obj_tag(v___x_1922_))
{
case 0:
{
lean_object* v_key_1923_; lean_object* v_val_1924_; uint8_t v___x_1925_; 
v_key_1923_ = lean_ctor_get(v___x_1922_, 0);
v_val_1924_ = lean_ctor_get(v___x_1922_, 1);
v___x_1925_ = lean_name_eq(v_x_1916_, v_key_1923_);
if (v___x_1925_ == 0)
{
lean_object* v___x_1926_; 
v___x_1926_ = lean_box(0);
return v___x_1926_;
}
else
{
lean_object* v___x_1927_; 
lean_inc(v_val_1924_);
v___x_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1927_, 0, v_val_1924_);
return v___x_1927_;
}
}
case 1:
{
lean_object* v_node_1928_; size_t v___x_1929_; size_t v___x_1930_; 
v_node_1928_ = lean_ctor_get(v___x_1922_, 0);
v___x_1929_ = ((size_t)5ULL);
v___x_1930_ = lean_usize_shift_right(v_x_1915_, v___x_1929_);
v_x_1914_ = v_node_1928_;
v_x_1915_ = v___x_1930_;
goto _start;
}
default: 
{
lean_object* v___x_1932_; 
v___x_1932_ = lean_box(0);
return v___x_1932_;
}
}
}
else
{
lean_object* v_ks_1933_; lean_object* v_vs_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v_ks_1933_ = lean_ctor_get(v_x_1914_, 0);
v_vs_1934_ = lean_ctor_get(v_x_1914_, 1);
v___x_1935_ = lean_unsigned_to_nat(0u);
v___x_1936_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_ks_1933_, v_vs_1934_, v___x_1935_, v_x_1916_);
return v___x_1936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_1937_, lean_object* v_x_1938_, lean_object* v_x_1939_){
_start:
{
size_t v_x_17692__boxed_1940_; lean_object* v_res_1941_; 
v_x_17692__boxed_1940_ = lean_unbox_usize(v_x_1938_);
lean_dec(v_x_1938_);
v_res_1941_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1937_, v_x_17692__boxed_1940_, v_x_1939_);
lean_dec(v_x_1939_);
lean_dec_ref(v_x_1937_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object* v_x_1942_, lean_object* v_x_1943_){
_start:
{
uint64_t v___y_1945_; 
if (lean_obj_tag(v_x_1943_) == 0)
{
uint64_t v___x_1948_; 
v___x_1948_ = 1723ULL;
v___y_1945_ = v___x_1948_;
goto v___jp_1944_;
}
else
{
uint64_t v_hash_1949_; 
v_hash_1949_ = lean_ctor_get_uint64(v_x_1943_, sizeof(void*)*2);
v___y_1945_ = v_hash_1949_;
goto v___jp_1944_;
}
v___jp_1944_:
{
size_t v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = lean_uint64_to_usize(v___y_1945_);
v___x_1947_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1942_, v___x_1946_, v_x_1943_);
return v___x_1947_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object* v_x_1950_, lean_object* v_x_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_1950_, v_x_1951_);
lean_dec(v_x_1951_);
lean_dec_ref(v_x_1950_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object* v_x_1953_, lean_object* v_x_1954_){
_start:
{
uint8_t v_stage_u2081_1955_; 
v_stage_u2081_1955_ = lean_ctor_get_uint8(v_x_1953_, sizeof(void*)*2);
if (v_stage_u2081_1955_ == 0)
{
lean_object* v_map_u2081_1956_; lean_object* v_map_u2082_1957_; lean_object* v___x_1958_; 
v_map_u2081_1956_ = lean_ctor_get(v_x_1953_, 0);
v_map_u2082_1957_ = lean_ctor_get(v_x_1953_, 1);
v___x_1958_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_1956_, v_x_1954_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v___x_1959_; 
v___x_1959_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_map_u2082_1957_, v_x_1954_);
return v___x_1959_;
}
else
{
return v___x_1958_;
}
}
else
{
lean_object* v_map_u2081_1960_; lean_object* v___x_1961_; 
v_map_u2081_1960_ = lean_ctor_get(v_x_1953_, 0);
v___x_1961_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_1960_, v_x_1954_);
return v___x_1961_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg___boxed(lean_object* v_x_1962_, lean_object* v_x_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_1962_, v_x_1963_);
lean_dec(v_x_1963_);
lean_dec_ref(v_x_1962_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object* v_firsts_1965_, lean_object* v_n_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1985_; lean_object* v_val_1986_; lean_object* v___x_1988_; lean_object* v___y_1990_; lean_object* v_env_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_1988_ = lean_st_ref_get(v___y_1968_);
v_env_2005_ = lean_ctor_get(v___x_1988_, 0);
lean_inc_ref(v_env_2005_);
lean_dec(v___x_1988_);
v___x_2006_ = l_Lean_Environment_constants(v_env_2005_);
v___x_2007_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v___x_2006_, v_n_1966_);
lean_dec_ref(v___x_2006_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v___x_2008_; 
v___x_2008_ = lean_box(0);
v___y_1990_ = v___x_2008_;
goto v___jp_1989_;
}
else
{
lean_object* v_val_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v_val_2009_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_val_2009_);
lean_dec_ref_known(v___x_2007_, 1);
v___x_2010_ = l_Lean_ConstantInfo_levelParams(v_val_2009_);
lean_dec(v_val_2009_);
v___x_2011_ = lean_box(0);
v___x_2012_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(v___x_2010_, v___x_2011_);
v___y_1990_ = v___x_2012_;
goto v___jp_1989_;
}
v___jp_1970_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1973_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_1974_ = l_Lean_Expr_const___override(v_n_1966_, v___y_1971_);
v___x_1975_ = lean_unsigned_to_nat(32u);
v___x_1976_ = lean_mk_empty_array_with_capacity(v___x_1975_);
lean_dec_ref(v___x_1976_);
v___x_1977_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2);
v___x_1978_ = lean_box(0);
v___x_1979_ = 0;
v___x_1980_ = l_Lean_MessageData_withExprHover(v___y_1972_, v___x_1974_, v___x_1977_, v___x_1978_, v___x_1978_, v___x_1978_, v___x_1979_);
v___x_1981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1973_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
v___x_1982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
lean_ctor_set(v___x_1982_, 1, v___x_1973_);
v___x_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
return v___x_1983_;
}
v___jp_1984_:
{
lean_object* v___x_1987_; 
v___x_1987_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1987_, 0, v_val_1986_);
v___y_1971_ = v___y_1985_;
v___y_1972_ = v___x_1987_;
goto v___jp_1970_;
}
v___jp_1989_:
{
lean_object* v___x_1991_; lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2004_; 
lean_inc(v_n_1966_);
v___x_1991_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_n_1966_, v___y_1968_);
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1994_ = v___x_1991_;
v_isShared_1995_ = v_isSharedCheck_2004_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1991_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2004_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
if (lean_obj_tag(v_a_1992_) == 0)
{
lean_object* v___x_1996_; 
v___x_1996_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_firsts_1965_, v_n_1966_);
if (lean_obj_tag(v___x_1996_) == 0)
{
uint8_t v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_2000_; 
v___x_1997_ = 1;
lean_inc(v_n_1966_);
v___x_1998_ = l_Lean_Name_toString(v_n_1966_, v___x_1997_);
if (v_isShared_1995_ == 0)
{
lean_ctor_set_tag(v___x_1994_, 3);
lean_ctor_set(v___x_1994_, 0, v___x_1998_);
v___x_2000_ = v___x_1994_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
v___y_1971_ = v___y_1990_;
v___y_1972_ = v___x_2000_;
goto v___jp_1970_;
}
}
else
{
lean_object* v_val_2002_; 
lean_del_object(v___x_1994_);
v_val_2002_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_val_2002_);
lean_dec_ref_known(v___x_1996_, 1);
v___y_1985_ = v___y_1990_;
v_val_1986_ = v_val_2002_;
goto v___jp_1984_;
}
}
else
{
lean_object* v_val_2003_; 
lean_del_object(v___x_1994_);
v_val_2003_ = lean_ctor_get(v_a_1992_, 0);
lean_inc(v_val_2003_);
lean_dec_ref_known(v_a_1992_, 1);
v___y_1985_ = v___y_1990_;
v_val_1986_ = v_val_2003_;
goto v___jp_1984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object* v_firsts_2013_, lean_object* v_n_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_firsts_2013_, v_n_2014_, v___y_2015_, v___y_2016_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v_firsts_2013_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object* v_a_2019_, lean_object* v_x_2020_, lean_object* v_x_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
if (lean_obj_tag(v_x_2020_) == 0)
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = l_List_reverse___redArg(v_x_2021_);
v___x_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2025_);
return v___x_2026_;
}
else
{
lean_object* v_head_2027_; lean_object* v_tail_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2046_; 
v_head_2027_ = lean_ctor_get(v_x_2020_, 0);
v_tail_2028_ = lean_ctor_get(v_x_2020_, 1);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_x_2020_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2030_ = v_x_2020_;
v_isShared_2031_ = v_isSharedCheck_2046_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_tail_2028_);
lean_inc(v_head_2027_);
lean_dec(v_x_2020_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2046_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2032_; 
v___x_2032_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_a_2019_, v_head_2027_, v___y_2022_, v___y_2023_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; lean_object* v___x_2035_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2033_);
lean_dec_ref_known(v___x_2032_, 1);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 1, v_x_2021_);
lean_ctor_set(v___x_2030_, 0, v_a_2033_);
v___x_2035_ = v___x_2030_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2033_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v_x_2021_);
v___x_2035_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
v_x_2020_ = v_tail_2028_;
v_x_2021_ = v___x_2035_;
goto _start;
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_del_object(v___x_2030_);
lean_dec(v_tail_2028_);
lean_dec(v_x_2021_);
v_a_2038_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2032_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2032_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object* v_a_2047_, lean_object* v_x_2048_, lean_object* v_x_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_2047_, v_x_2048_, v_x_2049_, v___y_2050_, v___y_2051_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v_a_2047_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object* v_val_2054_, lean_object* v___x_2055_, lean_object* v___x_2056_, lean_object* v_a_2057_, lean_object* v_b_2058_){
_start:
{
lean_object* v_it_2060_; lean_object* v_startInclusive_2061_; lean_object* v_endExclusive_2062_; 
if (lean_obj_tag(v_a_2057_) == 0)
{
lean_object* v_currPos_2067_; lean_object* v_searcher_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2094_; 
v_currPos_2067_ = lean_ctor_get(v_a_2057_, 0);
v_searcher_2068_ = lean_ctor_get(v_a_2057_, 1);
v_isSharedCheck_2094_ = !lean_is_exclusive(v_a_2057_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2070_ = v_a_2057_;
v_isShared_2071_ = v_isSharedCheck_2094_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_searcher_2068_);
lean_inc(v_currPos_2067_);
lean_dec(v_a_2057_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2094_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v_startInclusive_2072_; lean_object* v_endExclusive_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v_startInclusive_2072_ = lean_ctor_get(v___x_2055_, 1);
v_endExclusive_2073_ = lean_ctor_get(v___x_2055_, 2);
v___x_2074_ = lean_nat_sub(v_endExclusive_2073_, v_startInclusive_2072_);
v___x_2075_ = lean_nat_dec_eq(v_searcher_2068_, v___x_2074_);
lean_dec(v___x_2074_);
if (v___x_2075_ == 0)
{
uint32_t v___x_2076_; uint32_t v___x_2077_; uint8_t v___x_2078_; 
v___x_2076_ = 10;
v___x_2077_ = lean_string_utf8_get_fast(v_val_2054_, v_searcher_2068_);
v___x_2078_ = lean_uint32_dec_eq(v___x_2077_, v___x_2076_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; lean_object* v___x_2081_; 
v___x_2079_ = lean_string_utf8_next_fast(v_val_2054_, v_searcher_2068_);
lean_dec(v_searcher_2068_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 1, v___x_2079_);
v___x_2081_ = v___x_2070_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_currPos_2067_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
v_a_2057_ = v___x_2081_;
goto _start;
}
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v_slice_2087_; lean_object* v_nextIt_2089_; 
v___x_2084_ = lean_string_utf8_next_fast(v_val_2054_, v_searcher_2068_);
v___x_2085_ = lean_nat_sub(v___x_2084_, v_searcher_2068_);
v___x_2086_ = lean_nat_add(v_searcher_2068_, v___x_2085_);
lean_dec(v___x_2085_);
v_slice_2087_ = l_String_Slice_subslice_x21(v___x_2055_, v_currPos_2067_, v_searcher_2068_);
lean_inc(v___x_2086_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 1, v___x_2086_);
lean_ctor_set(v___x_2070_, 0, v___x_2086_);
v_nextIt_2089_ = v___x_2070_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2086_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v___x_2086_);
v_nextIt_2089_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
lean_object* v_startInclusive_2090_; lean_object* v_endExclusive_2091_; 
v_startInclusive_2090_ = lean_ctor_get(v_slice_2087_, 0);
lean_inc(v_startInclusive_2090_);
v_endExclusive_2091_ = lean_ctor_get(v_slice_2087_, 1);
lean_inc(v_endExclusive_2091_);
lean_dec_ref(v_slice_2087_);
v_it_2060_ = v_nextIt_2089_;
v_startInclusive_2061_ = v_startInclusive_2090_;
v_endExclusive_2062_ = v_endExclusive_2091_;
goto v___jp_2059_;
}
}
}
else
{
lean_object* v___x_2093_; 
lean_del_object(v___x_2070_);
lean_dec(v_searcher_2068_);
v___x_2093_ = lean_box(1);
lean_inc(v___x_2056_);
v_it_2060_ = v___x_2093_;
v_startInclusive_2061_ = v_currPos_2067_;
v_endExclusive_2062_ = v___x_2056_;
goto v___jp_2059_;
}
}
}
else
{
lean_dec(v___x_2056_);
return v_b_2058_;
}
v___jp_2059_:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2063_ = lean_string_utf8_extract_fast(v_val_2054_, v_startInclusive_2061_, v_endExclusive_2062_);
lean_dec(v_endExclusive_2062_);
lean_dec(v_startInclusive_2061_);
v___x_2064_ = l_Lean_stringToMessageData(v___x_2063_);
v___x_2065_ = lean_array_push(v_b_2058_, v___x_2064_);
v_a_2057_ = v_it_2060_;
v_b_2058_ = v___x_2065_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object* v_val_2095_, lean_object* v___x_2096_, lean_object* v___x_2097_, lean_object* v_a_2098_, lean_object* v_b_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2095_, v___x_2096_, v___x_2097_, v_a_2098_, v_b_2099_);
lean_dec_ref(v___x_2096_);
lean_dec_ref(v_val_2095_);
return v_res_2100_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2(void){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1));
v___x_2105_ = l_Lean_stringToMessageData(v___x_2104_);
return v___x_2105_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4(void){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3));
v___x_2108_ = l_Lean_stringToMessageData(v___x_2107_);
return v___x_2108_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6(void){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5));
v___x_2111_ = l_Lean_stringToMessageData(v___x_2110_);
return v___x_2111_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8));
v___x_2116_ = l_Lean_MessageData_ofFormat(v___x_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_x_2119_, lean_object* v_x_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
if (lean_obj_tag(v_x_2119_) == 0)
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = l_List_reverse___redArg(v_x_2120_);
v___x_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
return v___x_2125_;
}
else
{
lean_object* v_head_2126_; lean_object* v_tail_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2224_; 
v_head_2126_ = lean_ctor_get(v_x_2119_, 0);
v_tail_2127_ = lean_ctor_get(v_x_2119_, 1);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_x_2119_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2129_ = v_x_2119_;
v_isShared_2130_ = v_isSharedCheck_2224_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_tail_2127_);
lean_inc(v_head_2126_);
lean_dec(v_x_2119_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2224_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v_snd_2144_; lean_object* v_fst_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2223_; 
v_snd_2144_ = lean_ctor_get(v_head_2126_, 1);
v_fst_2145_ = lean_ctor_get(v_head_2126_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_head_2126_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2147_ = v_head_2126_;
v_isShared_2148_ = v_isSharedCheck_2223_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_snd_2144_);
lean_inc(v_fst_2145_);
lean_dec(v_head_2126_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2223_;
goto v_resetjp_2146_;
}
v___jp_2131_:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2141_; 
v___x_2136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___y_2133_);
lean_ctor_set(v___x_2136_, 1, v___y_2135_);
v___x_2137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2136_);
lean_ctor_set(v___x_2137_, 1, v___y_2132_);
v___x_2138_ = l_Lean_MessageData_nestD(v___x_2137_);
lean_inc_ref(v___y_2134_);
v___x_2139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___y_2134_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 1, v_x_2120_);
lean_ctor_set(v___x_2129_, 0, v___x_2139_);
v___x_2141_ = v___x_2129_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2139_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_x_2120_);
v___x_2141_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
v_x_2119_ = v_tail_2127_;
v_x_2120_ = v___x_2141_;
goto _start;
}
}
v_resetjp_2146_:
{
lean_object* v_fst_2149_; lean_object* v_snd_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2222_; 
v_fst_2149_ = lean_ctor_get(v_snd_2144_, 0);
v_snd_2150_ = lean_ctor_get(v_snd_2144_, 1);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_snd_2144_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2152_ = v_snd_2144_;
v_isShared_2153_ = v_isSharedCheck_2222_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_snd_2150_);
lean_inc(v_fst_2149_);
lean_dec(v_snd_2144_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2222_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v_a_2177_; lean_object* v___y_2193_; lean_object* v___x_2202_; 
v___x_2202_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2118_, v_fst_2145_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v___x_2203_; 
v___x_2203_ = l_Lean_MessageData_nil;
v_a_2177_ = v___x_2203_;
goto v___jp_2176_;
}
else
{
lean_object* v_val_2204_; 
v_val_2204_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_val_2204_);
lean_dec_ref_known(v___x_2202_, 1);
if (lean_obj_tag(v_val_2204_) == 0)
{
lean_object* v_size_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___x_2213_; uint8_t v___x_2214_; 
v_size_2205_ = lean_ctor_get(v_val_2204_, 0);
v___x_2206_ = lean_mk_empty_array_with_capacity(v_size_2205_);
v___x_2207_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v___x_2206_, v_val_2204_);
v___x_2208_ = lean_array_get_size(v___x_2207_);
v___x_2213_ = lean_unsigned_to_nat(0u);
v___x_2214_ = lean_nat_dec_eq(v___x_2208_, v___x_2213_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___y_2218_; uint8_t v___x_2220_; 
v___x_2215_ = lean_unsigned_to_nat(1u);
v___x_2216_ = lean_nat_sub(v___x_2208_, v___x_2215_);
v___x_2220_ = lean_nat_dec_le(v___x_2213_, v___x_2216_);
if (v___x_2220_ == 0)
{
lean_inc(v___x_2216_);
v___y_2218_ = v___x_2216_;
goto v___jp_2217_;
}
else
{
v___y_2218_ = v___x_2213_;
goto v___jp_2217_;
}
v___jp_2217_:
{
uint8_t v___x_2219_; 
v___x_2219_ = lean_nat_dec_le(v___y_2218_, v___x_2216_);
if (v___x_2219_ == 0)
{
lean_dec(v___x_2216_);
lean_inc(v___y_2218_);
v___y_2210_ = v___y_2218_;
v___y_2211_ = v___y_2218_;
goto v___jp_2209_;
}
else
{
v___y_2210_ = v___y_2218_;
v___y_2211_ = v___x_2216_;
goto v___jp_2209_;
}
}
}
else
{
v___y_2193_ = v___x_2207_;
goto v___jp_2192_;
}
v___jp_2209_:
{
lean_object* v___x_2212_; 
v___x_2212_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v___x_2208_, v___x_2207_, v___y_2210_, v___y_2211_);
lean_dec(v___y_2211_);
v___y_2193_ = v___x_2212_;
goto v___jp_2192_;
}
}
else
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Lean_MessageData_nil;
v_a_2177_ = v___x_2221_;
goto v___jp_2176_;
}
}
v___jp_2154_:
{
lean_object* v___x_2160_; 
if (v_isShared_2153_ == 0)
{
lean_ctor_set_tag(v___x_2152_, 7);
lean_ctor_set(v___x_2152_, 1, v___y_2158_);
lean_ctor_set(v___x_2152_, 0, v___y_2156_);
v___x_2160_ = v___x_2152_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___y_2156_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v___y_2158_);
v___x_2160_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
if (lean_obj_tag(v_snd_2150_) == 0)
{
lean_object* v___x_2161_; 
lean_del_object(v___x_2147_);
v___x_2161_ = l_Lean_MessageData_nil;
v___y_2132_ = v___y_2155_;
v___y_2133_ = v___x_2160_;
v___y_2134_ = v___y_2157_;
v___y_2135_ = v___x_2161_;
goto v___jp_2131_;
}
else
{
lean_object* v_val_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2173_; 
v_val_2162_ = lean_ctor_get(v_snd_2150_, 0);
lean_inc_n(v_val_2162_, 2);
lean_dec_ref_known(v_snd_2150_, 1);
v___x_2163_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2164_ = lean_unsigned_to_nat(0u);
v___x_2165_ = lean_string_utf8_byte_size(v_val_2162_);
v___x_2166_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2166_, 0, v_val_2162_);
lean_ctor_set(v___x_2166_, 1, v___x_2164_);
lean_ctor_set(v___x_2166_, 2, v___x_2165_);
v___x_2167_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v___x_2166_);
v___x_2168_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0));
v___x_2169_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2162_, v___x_2166_, v___x_2165_, v___x_2167_, v___x_2168_);
lean_dec_ref_known(v___x_2166_, 3);
lean_dec(v_val_2162_);
v___x_2170_ = lean_array_to_list(v___x_2169_);
v___x_2171_ = l_Lean_MessageData_joinSep(v___x_2170_, v___x_2163_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set_tag(v___x_2147_, 7);
lean_ctor_set(v___x_2147_, 1, v___x_2171_);
lean_ctor_set(v___x_2147_, 0, v___x_2163_);
v___x_2173_ = v___x_2147_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2163_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
v___y_2132_ = v___y_2155_;
v___y_2133_ = v___x_2160_;
v___y_2134_ = v___y_2157_;
v___y_2135_ = v___x_2173_;
goto v___jp_2131_;
}
}
}
}
v___jp_2176_:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; 
v___x_2178_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2);
v___x_2179_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
lean_inc(v_fst_2145_);
v___x_2180_ = l_Lean_MessageData_ofName(v_fst_2145_);
v___x_2181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2179_);
lean_ctor_set(v___x_2181_, 1, v___x_2180_);
v___x_2182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
lean_ctor_set(v___x_2182_, 1, v___x_2179_);
v___x_2183_ = 1;
v___x_2184_ = l_Lean_Name_toString(v_fst_2145_, v___x_2183_);
v___x_2185_ = lean_string_dec_eq(v___x_2184_, v_fst_2149_);
lean_dec_ref(v___x_2184_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2186_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4);
v___x_2187_ = l_Lean_stringToMessageData(v_fst_2149_);
v___x_2188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2186_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
v___x_2189_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6);
v___x_2190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2188_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
v___y_2155_ = v_a_2177_;
v___y_2156_ = v___x_2182_;
v___y_2157_ = v___x_2178_;
v___y_2158_ = v___x_2190_;
goto v___jp_2154_;
}
else
{
lean_object* v___x_2191_; 
lean_dec(v_fst_2149_);
v___x_2191_ = l_Lean_MessageData_nil;
v___y_2155_ = v_a_2177_;
v___y_2156_ = v___x_2182_;
v___y_2157_ = v___x_2178_;
v___y_2158_ = v___x_2191_;
goto v___jp_2154_;
}
}
v___jp_2192_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2194_ = lean_array_to_list(v___y_2193_);
v___x_2195_ = lean_box(0);
v___x_2196_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_2117_, v___x_2194_, v___x_2195_, v___y_2121_, v___y_2122_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_a_2197_);
lean_dec_ref_known(v___x_2196_, 1);
v___x_2198_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2199_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9);
v___x_2200_ = l_Lean_MessageData_joinSep(v_a_2197_, v___x_2199_);
v___x_2201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2198_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
v_a_2177_ = v___x_2201_;
goto v___jp_2176_;
}
else
{
lean_del_object(v___x_2152_);
lean_dec(v_snd_2150_);
lean_dec(v_fst_2149_);
lean_del_object(v___x_2147_);
lean_dec(v_fst_2145_);
lean_del_object(v___x_2129_);
lean_dec(v_tail_2127_);
lean_dec(v_x_2120_);
return v___x_2196_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_x_2227_, lean_object* v_x_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_2225_, v_a_2226_, v_x_2227_, v_x_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v_a_2226_);
lean_dec(v_a_2225_);
return v_res_2232_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(uint8_t v___y_2234_, uint8_t v_suppressElabErrors_2235_, lean_object* v_x_2236_){
_start:
{
if (lean_obj_tag(v_x_2236_) == 1)
{
lean_object* v_pre_2237_; 
v_pre_2237_ = lean_ctor_get(v_x_2236_, 0);
if (lean_obj_tag(v_pre_2237_) == 0)
{
lean_object* v_str_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v_str_2238_ = lean_ctor_get(v_x_2236_, 1);
v___x_2239_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0));
v___x_2240_ = lean_string_dec_eq(v_str_2238_, v___x_2239_);
if (v___x_2240_ == 0)
{
return v___y_2234_;
}
else
{
return v_suppressElabErrors_2235_;
}
}
else
{
return v___y_2234_;
}
}
else
{
return v___y_2234_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed(lean_object* v___y_2241_, lean_object* v_suppressElabErrors_2242_, lean_object* v_x_2243_){
_start:
{
uint8_t v___y_18309__boxed_2244_; uint8_t v_suppressElabErrors_boxed_2245_; uint8_t v_res_2246_; lean_object* v_r_2247_; 
v___y_18309__boxed_2244_ = lean_unbox(v___y_2241_);
v_suppressElabErrors_boxed_2245_ = lean_unbox(v_suppressElabErrors_2242_);
v_res_2246_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(v___y_18309__boxed_2244_, v_suppressElabErrors_boxed_2245_, v_x_2243_);
lean_dec(v_x_2243_);
v_r_2247_ = lean_box(v_res_2246_);
return v_r_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(lean_object* v_ref_2248_, lean_object* v_msgData_2249_, uint8_t v_severity_2250_, uint8_t v_isSilent_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v___y_2256_; uint8_t v___y_2257_; lean_object* v___y_2258_; uint8_t v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; uint8_t v___y_2320_; uint8_t v___y_2321_; lean_object* v___y_2322_; uint8_t v___y_2323_; lean_object* v___y_2324_; uint8_t v___y_2348_; lean_object* v___y_2349_; uint8_t v___y_2350_; uint8_t v___y_2351_; lean_object* v___y_2352_; uint8_t v___y_2356_; uint8_t v___y_2357_; uint8_t v___y_2358_; uint8_t v___x_2373_; uint8_t v___y_2375_; uint8_t v___y_2376_; uint8_t v___y_2377_; uint8_t v___y_2379_; uint8_t v___x_2391_; 
v___x_2373_ = 2;
v___x_2391_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2250_, v___x_2373_);
if (v___x_2391_ == 0)
{
v___y_2379_ = v___x_2391_;
goto v___jp_2378_;
}
else
{
uint8_t v___x_2392_; 
lean_inc_ref(v_msgData_2249_);
v___x_2392_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2249_);
v___y_2379_ = v___x_2392_;
goto v___jp_2378_;
}
v___jp_2255_:
{
lean_object* v___x_2264_; 
v___x_2264_ = l_Lean_Elab_Command_getScope___redArg(v___y_2263_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v___x_2266_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_a_2265_);
lean_dec_ref_known(v___x_2264_, 1);
v___x_2266_ = l_Lean_Elab_Command_getScope___redArg(v___y_2263_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2302_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2269_ = v___x_2266_;
v_isShared_2270_ = v_isSharedCheck_2302_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2266_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2302_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2271_; lean_object* v_currNamespace_2272_; lean_object* v_openDecls_2273_; lean_object* v_env_2274_; lean_object* v_messages_2275_; lean_object* v_scopes_2276_; lean_object* v_usedQuotCtxts_2277_; lean_object* v_nextMacroScope_2278_; lean_object* v_maxRecDepth_2279_; lean_object* v_ngen_2280_; lean_object* v_auxDeclNGen_2281_; lean_object* v_infoState_2282_; lean_object* v_traceState_2283_; lean_object* v_snapshotTasks_2284_; lean_object* v_prevLinterStates_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2301_; 
v___x_2271_ = lean_st_ref_take(v___y_2263_);
v_currNamespace_2272_ = lean_ctor_get(v_a_2265_, 2);
lean_inc(v_currNamespace_2272_);
lean_dec(v_a_2265_);
v_openDecls_2273_ = lean_ctor_get(v_a_2267_, 3);
lean_inc(v_openDecls_2273_);
lean_dec(v_a_2267_);
v_env_2274_ = lean_ctor_get(v___x_2271_, 0);
v_messages_2275_ = lean_ctor_get(v___x_2271_, 1);
v_scopes_2276_ = lean_ctor_get(v___x_2271_, 2);
v_usedQuotCtxts_2277_ = lean_ctor_get(v___x_2271_, 3);
v_nextMacroScope_2278_ = lean_ctor_get(v___x_2271_, 4);
v_maxRecDepth_2279_ = lean_ctor_get(v___x_2271_, 5);
v_ngen_2280_ = lean_ctor_get(v___x_2271_, 6);
v_auxDeclNGen_2281_ = lean_ctor_get(v___x_2271_, 7);
v_infoState_2282_ = lean_ctor_get(v___x_2271_, 8);
v_traceState_2283_ = lean_ctor_get(v___x_2271_, 9);
v_snapshotTasks_2284_ = lean_ctor_get(v___x_2271_, 10);
v_prevLinterStates_2285_ = lean_ctor_get(v___x_2271_, 11);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2287_ = v___x_2271_;
v_isShared_2288_ = v_isSharedCheck_2301_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_prevLinterStates_2285_);
lean_inc(v_snapshotTasks_2284_);
lean_inc(v_traceState_2283_);
lean_inc(v_infoState_2282_);
lean_inc(v_auxDeclNGen_2281_);
lean_inc(v_ngen_2280_);
lean_inc(v_maxRecDepth_2279_);
lean_inc(v_nextMacroScope_2278_);
lean_inc(v_usedQuotCtxts_2277_);
lean_inc(v_scopes_2276_);
lean_inc(v_messages_2275_);
lean_inc(v_env_2274_);
lean_dec(v___x_2271_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2301_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2294_; 
v___x_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2289_, 0, v_currNamespace_2272_);
lean_ctor_set(v___x_2289_, 1, v_openDecls_2273_);
v___x_2290_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
lean_ctor_set(v___x_2290_, 1, v___y_2262_);
lean_inc_ref(v___y_2261_);
lean_inc_ref(v___y_2260_);
v___x_2291_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2291_, 0, v___y_2260_);
lean_ctor_set(v___x_2291_, 1, v___y_2256_);
lean_ctor_set(v___x_2291_, 2, v___y_2258_);
lean_ctor_set(v___x_2291_, 3, v___y_2261_);
lean_ctor_set(v___x_2291_, 4, v___x_2290_);
lean_ctor_set_uint8(v___x_2291_, sizeof(void*)*5, v___y_2257_);
lean_ctor_set_uint8(v___x_2291_, sizeof(void*)*5 + 1, v___y_2259_);
lean_ctor_set_uint8(v___x_2291_, sizeof(void*)*5 + 2, v_isSilent_2251_);
v___x_2292_ = l_Lean_MessageLog_add(v___x_2291_, v_messages_2275_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 1, v___x_2292_);
v___x_2294_ = v___x_2287_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_env_2274_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v___x_2292_);
lean_ctor_set(v_reuseFailAlloc_2300_, 2, v_scopes_2276_);
lean_ctor_set(v_reuseFailAlloc_2300_, 3, v_usedQuotCtxts_2277_);
lean_ctor_set(v_reuseFailAlloc_2300_, 4, v_nextMacroScope_2278_);
lean_ctor_set(v_reuseFailAlloc_2300_, 5, v_maxRecDepth_2279_);
lean_ctor_set(v_reuseFailAlloc_2300_, 6, v_ngen_2280_);
lean_ctor_set(v_reuseFailAlloc_2300_, 7, v_auxDeclNGen_2281_);
lean_ctor_set(v_reuseFailAlloc_2300_, 8, v_infoState_2282_);
lean_ctor_set(v_reuseFailAlloc_2300_, 9, v_traceState_2283_);
lean_ctor_set(v_reuseFailAlloc_2300_, 10, v_snapshotTasks_2284_);
lean_ctor_set(v_reuseFailAlloc_2300_, 11, v_prevLinterStates_2285_);
v___x_2294_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2298_; 
v___x_2295_ = lean_st_ref_put(v___y_2263_, v___x_2294_);
v___x_2296_ = lean_box(0);
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 0, v___x_2296_);
v___x_2298_ = v___x_2269_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2296_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_dec(v_a_2265_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2256_);
v_a_2303_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2266_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2266_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2256_);
v_a_2311_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2264_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2264_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
v___jp_2319_:
{
lean_object* v_fileName_2325_; lean_object* v_fileMap_2326_; uint8_t v_suppressElabErrors_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2346_; 
v_fileName_2325_ = lean_ctor_get(v___y_2252_, 0);
v_fileMap_2326_ = lean_ctor_get(v___y_2252_, 1);
v_suppressElabErrors_2327_ = lean_ctor_get_uint8(v___y_2252_, sizeof(void*)*10);
v___x_2328_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2249_);
v___x_2329_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v___x_2328_, v___y_2253_);
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2346_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2346_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_inc_ref_n(v_fileMap_2326_, 2);
v___x_2334_ = l_Lean_FileMap_toPosition(v_fileMap_2326_, v___y_2322_);
lean_dec(v___y_2322_);
v___x_2335_ = l_Lean_FileMap_toPosition(v_fileMap_2326_, v___y_2324_);
lean_dec(v___y_2324_);
v___x_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2335_);
v___x_2337_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
if (v_suppressElabErrors_2327_ == 0)
{
lean_del_object(v___x_2332_);
v___y_2256_ = v___x_2334_;
v___y_2257_ = v___y_2321_;
v___y_2258_ = v___x_2336_;
v___y_2259_ = v___y_2323_;
v___y_2260_ = v_fileName_2325_;
v___y_2261_ = v___x_2337_;
v___y_2262_ = v_a_2330_;
v___y_2263_ = v___y_2253_;
goto v___jp_2255_;
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___f_2340_; uint8_t v___x_2341_; 
v___x_2338_ = lean_box(v___y_2320_);
v___x_2339_ = lean_box(v_suppressElabErrors_2327_);
v___f_2340_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2340_, 0, v___x_2338_);
lean_closure_set(v___f_2340_, 1, v___x_2339_);
lean_inc(v_a_2330_);
v___x_2341_ = l_Lean_MessageData_hasTag(v___f_2340_, v_a_2330_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; lean_object* v___x_2344_; 
lean_dec_ref_known(v___x_2336_, 1);
lean_dec_ref(v___x_2334_);
lean_dec(v_a_2330_);
v___x_2342_ = lean_box(0);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2342_);
v___x_2344_ = v___x_2332_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2342_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
else
{
lean_del_object(v___x_2332_);
v___y_2256_ = v___x_2334_;
v___y_2257_ = v___y_2321_;
v___y_2258_ = v___x_2336_;
v___y_2259_ = v___y_2323_;
v___y_2260_ = v_fileName_2325_;
v___y_2261_ = v___x_2337_;
v___y_2262_ = v_a_2330_;
v___y_2263_ = v___y_2253_;
goto v___jp_2255_;
}
}
}
}
v___jp_2347_:
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Lean_Syntax_getTailPos_x3f(v___y_2349_, v___y_2350_);
lean_dec(v___y_2349_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_inc(v___y_2352_);
v___y_2320_ = v___y_2348_;
v___y_2321_ = v___y_2350_;
v___y_2322_ = v___y_2352_;
v___y_2323_ = v___y_2351_;
v___y_2324_ = v___y_2352_;
goto v___jp_2319_;
}
else
{
lean_object* v_val_2354_; 
v_val_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_val_2354_);
lean_dec_ref_known(v___x_2353_, 1);
v___y_2320_ = v___y_2348_;
v___y_2321_ = v___y_2350_;
v___y_2322_ = v___y_2352_;
v___y_2323_ = v___y_2351_;
v___y_2324_ = v_val_2354_;
goto v___jp_2319_;
}
}
v___jp_2355_:
{
lean_object* v___x_2359_; 
v___x_2359_ = l_Lean_Elab_Command_getRef___redArg(v___y_2252_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v_ref_2361_; lean_object* v___x_2362_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2360_);
lean_dec_ref_known(v___x_2359_, 1);
v_ref_2361_ = l_Lean_replaceRef(v_ref_2248_, v_a_2360_);
lean_dec(v_a_2360_);
v___x_2362_ = l_Lean_Syntax_getPos_x3f(v_ref_2361_, v___y_2357_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v___x_2363_; 
v___x_2363_ = lean_unsigned_to_nat(0u);
v___y_2348_ = v___y_2356_;
v___y_2349_ = v_ref_2361_;
v___y_2350_ = v___y_2357_;
v___y_2351_ = v___y_2358_;
v___y_2352_ = v___x_2363_;
goto v___jp_2347_;
}
else
{
lean_object* v_val_2364_; 
v_val_2364_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_val_2364_);
lean_dec_ref_known(v___x_2362_, 1);
v___y_2348_ = v___y_2356_;
v___y_2349_ = v_ref_2361_;
v___y_2350_ = v___y_2357_;
v___y_2351_ = v___y_2358_;
v___y_2352_ = v_val_2364_;
goto v___jp_2347_;
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec_ref(v_msgData_2249_);
v_a_2365_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2359_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2359_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
v___jp_2374_:
{
if (v___y_2377_ == 0)
{
v___y_2356_ = v___y_2375_;
v___y_2357_ = v___y_2376_;
v___y_2358_ = v_severity_2250_;
goto v___jp_2355_;
}
else
{
v___y_2356_ = v___y_2375_;
v___y_2357_ = v___y_2376_;
v___y_2358_ = v___x_2373_;
goto v___jp_2355_;
}
}
v___jp_2378_:
{
if (v___y_2379_ == 0)
{
lean_object* v___x_2380_; lean_object* v_scopes_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v_opts_2384_; uint8_t v___x_2385_; uint8_t v___x_2386_; 
v___x_2380_ = lean_st_ref_get(v___y_2253_);
v_scopes_2381_ = lean_ctor_get(v___x_2380_, 2);
lean_inc(v_scopes_2381_);
lean_dec(v___x_2380_);
v___x_2382_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2383_ = l_List_head_x21___redArg(v___x_2382_, v_scopes_2381_);
lean_dec(v_scopes_2381_);
v_opts_2384_ = lean_ctor_get(v___x_2383_, 1);
lean_inc_ref(v_opts_2384_);
lean_dec(v___x_2383_);
v___x_2385_ = 1;
v___x_2386_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2250_, v___x_2385_);
if (v___x_2386_ == 0)
{
lean_dec_ref(v_opts_2384_);
v___y_2375_ = v___y_2379_;
v___y_2376_ = v___y_2379_;
v___y_2377_ = v___x_2386_;
goto v___jp_2374_;
}
else
{
lean_object* v___x_2387_; uint8_t v___x_2388_; 
v___x_2387_ = l_Lean_warningAsError;
v___x_2388_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_2384_, v___x_2387_);
lean_dec_ref(v_opts_2384_);
v___y_2375_ = v___y_2379_;
v___y_2376_ = v___y_2379_;
v___y_2377_ = v___x_2388_;
goto v___jp_2374_;
}
}
else
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
lean_dec_ref(v_msgData_2249_);
v___x_2389_ = lean_box(0);
v___x_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
return v___x_2390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___boxed(lean_object* v_ref_2393_, lean_object* v_msgData_2394_, lean_object* v_severity_2395_, lean_object* v_isSilent_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
uint8_t v_severity_boxed_2400_; uint8_t v_isSilent_boxed_2401_; lean_object* v_res_2402_; 
v_severity_boxed_2400_ = lean_unbox(v_severity_2395_);
v_isSilent_boxed_2401_ = lean_unbox(v_isSilent_2396_);
v_res_2402_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_ref_2393_, v_msgData_2394_, v_severity_boxed_2400_, v_isSilent_boxed_2401_, v___y_2397_, v___y_2398_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v_ref_2393_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(lean_object* v_msgData_2403_, uint8_t v_severity_2404_, uint8_t v_isSilent_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Lean_Elab_Command_getRef___redArg(v___y_2406_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v___x_2411_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2410_);
lean_dec_ref_known(v___x_2409_, 1);
v___x_2411_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_a_2410_, v_msgData_2403_, v_severity_2404_, v_isSilent_2405_, v___y_2406_, v___y_2407_);
lean_dec(v_a_2410_);
return v___x_2411_;
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec_ref(v_msgData_2403_);
v_a_2412_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2409_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2409_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26___boxed(lean_object* v_msgData_2420_, lean_object* v_severity_2421_, lean_object* v_isSilent_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
uint8_t v_severity_boxed_2426_; uint8_t v_isSilent_boxed_2427_; lean_object* v_res_2428_; 
v_severity_boxed_2426_ = lean_unbox(v_severity_2421_);
v_isSilent_boxed_2427_ = lean_unbox(v_isSilent_2422_);
v_res_2428_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_2420_, v_severity_boxed_2426_, v_isSilent_boxed_2427_, v___y_2423_, v___y_2424_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object* v_msgData_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
uint8_t v___x_2433_; uint8_t v___x_2434_; lean_object* v___x_2435_; 
v___x_2433_ = 0;
v___x_2434_ = 0;
v___x_2435_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_2429_, v___x_2433_, v___x_2434_, v___y_2430_, v___y_2431_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object* v_msgData_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v_msgData_2436_, v___y_2437_, v___y_2438_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object* v_init_2441_, lean_object* v_x_2442_){
_start:
{
if (lean_obj_tag(v_x_2442_) == 0)
{
lean_object* v_k_2444_; lean_object* v_v_2445_; lean_object* v_l_2446_; lean_object* v_r_2447_; lean_object* v___x_2448_; lean_object* v_a_2449_; lean_object* v_a_2450_; lean_object* v___x_2451_; 
v_k_2444_ = lean_ctor_get(v_x_2442_, 1);
lean_inc(v_k_2444_);
v_v_2445_ = lean_ctor_get(v_x_2442_, 2);
lean_inc(v_v_2445_);
v_l_2446_ = lean_ctor_get(v_x_2442_, 3);
lean_inc(v_l_2446_);
v_r_2447_ = lean_ctor_get(v_x_2442_, 4);
lean_inc(v_r_2447_);
lean_dec_ref_known(v_x_2442_, 5);
v___x_2448_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_2441_, v_l_2446_);
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc(v_a_2449_);
lean_dec_ref(v___x_2448_);
v_a_2450_ = lean_ctor_get(v_a_2449_, 0);
lean_inc(v_a_2450_);
lean_dec(v_a_2449_);
v___x_2451_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2444_, v_v_2445_, v_a_2450_);
v_init_2441_ = v___x_2451_;
v_x_2442_ = v_r_2447_;
goto _start;
}
else
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2453_, 0, v_init_2441_);
v___x_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2453_);
return v___x_2454_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object* v_init_2455_, lean_object* v_x_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_2455_, v_x_2456_);
return v_res_2458_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(uint8_t v___x_2459_, lean_object* v_x1_2460_, lean_object* v_x2_2461_){
_start:
{
lean_object* v_fst_2462_; lean_object* v_fst_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; uint8_t v___x_2466_; 
v_fst_2462_ = lean_ctor_get(v_x1_2460_, 0);
lean_inc(v_fst_2462_);
lean_dec_ref(v_x1_2460_);
v_fst_2463_ = lean_ctor_get(v_x2_2461_, 0);
lean_inc(v_fst_2463_);
lean_dec_ref(v_x2_2461_);
v___x_2464_ = l_Lean_Name_toString(v_fst_2462_, v___x_2459_);
v___x_2465_ = l_Lean_Name_toString(v_fst_2463_, v___x_2459_);
v___x_2466_ = lean_string_dec_lt(v___x_2464_, v___x_2465_);
lean_dec_ref(v___x_2465_);
lean_dec_ref(v___x_2464_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0___boxed(lean_object* v___x_2467_, lean_object* v_x1_2468_, lean_object* v_x2_2469_){
_start:
{
uint8_t v___x_18652__boxed_2470_; uint8_t v_res_2471_; lean_object* v_r_2472_; 
v___x_18652__boxed_2470_ = lean_unbox(v___x_2467_);
v_res_2471_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_18652__boxed_2470_, v_x1_2468_, v_x2_2469_);
v_r_2472_ = lean_box(v_res_2471_);
return v_r_2472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(lean_object* v_hi_2473_, lean_object* v_pivot_2474_, lean_object* v_as_2475_, lean_object* v_i_2476_, lean_object* v_k_2477_){
_start:
{
uint8_t v___x_2478_; 
v___x_2478_ = lean_nat_dec_lt(v_k_2477_, v_hi_2473_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
lean_dec(v_k_2477_);
lean_dec_ref(v_pivot_2474_);
v___x_2479_ = lean_array_fswap(v_as_2475_, v_i_2476_, v_hi_2473_);
v___x_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2480_, 0, v_i_2476_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
return v___x_2480_;
}
else
{
lean_object* v___x_2481_; lean_object* v_fst_2482_; lean_object* v_fst_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; 
v___x_2481_ = lean_array_fget_borrowed(v_as_2475_, v_k_2477_);
v_fst_2482_ = lean_ctor_get(v___x_2481_, 0);
v_fst_2483_ = lean_ctor_get(v_pivot_2474_, 0);
lean_inc(v_fst_2482_);
v___x_2484_ = l_Lean_Name_toString(v_fst_2482_, v___x_2478_);
lean_inc(v_fst_2483_);
v___x_2485_ = l_Lean_Name_toString(v_fst_2483_, v___x_2478_);
v___x_2486_ = lean_string_dec_lt(v___x_2484_, v___x_2485_);
lean_dec_ref(v___x_2485_);
lean_dec_ref(v___x_2484_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2487_ = lean_unsigned_to_nat(1u);
v___x_2488_ = lean_nat_add(v_k_2477_, v___x_2487_);
lean_dec(v_k_2477_);
v_k_2477_ = v___x_2488_;
goto _start;
}
else
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2490_ = lean_array_fswap(v_as_2475_, v_i_2476_, v_k_2477_);
v___x_2491_ = lean_unsigned_to_nat(1u);
v___x_2492_ = lean_nat_add(v_i_2476_, v___x_2491_);
lean_dec(v_i_2476_);
v___x_2493_ = lean_nat_add(v_k_2477_, v___x_2491_);
lean_dec(v_k_2477_);
v_as_2475_ = v___x_2490_;
v_i_2476_ = v___x_2492_;
v_k_2477_ = v___x_2493_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg___boxed(lean_object* v_hi_2495_, lean_object* v_pivot_2496_, lean_object* v_as_2497_, lean_object* v_i_2498_, lean_object* v_k_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_2495_, v_pivot_2496_, v_as_2497_, v_i_2498_, v_k_2499_);
lean_dec(v_hi_2495_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(lean_object* v_n_2501_, lean_object* v_as_2502_, lean_object* v_lo_2503_, lean_object* v_hi_2504_){
_start:
{
lean_object* v___y_2506_; uint8_t v___x_2516_; 
v___x_2516_ = lean_nat_dec_lt(v_lo_2503_, v_hi_2504_);
if (v___x_2516_ == 0)
{
lean_dec(v_lo_2503_);
return v_as_2502_;
}
else
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v_mid_2519_; lean_object* v___y_2521_; lean_object* v___y_2527_; lean_object* v___x_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v___x_2517_ = lean_nat_add(v_lo_2503_, v_hi_2504_);
v___x_2518_ = lean_unsigned_to_nat(1u);
v_mid_2519_ = lean_nat_shiftr(v___x_2517_, v___x_2518_);
lean_dec(v___x_2517_);
v___x_2532_ = lean_array_fget_borrowed(v_as_2502_, v_mid_2519_);
v___x_2533_ = lean_array_fget_borrowed(v_as_2502_, v_lo_2503_);
lean_inc(v___x_2533_);
lean_inc(v___x_2532_);
v___x_2534_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2516_, v___x_2532_, v___x_2533_);
if (v___x_2534_ == 0)
{
v___y_2527_ = v_as_2502_;
goto v___jp_2526_;
}
else
{
lean_object* v___x_2535_; 
v___x_2535_ = lean_array_fswap(v_as_2502_, v_lo_2503_, v_mid_2519_);
v___y_2527_ = v___x_2535_;
goto v___jp_2526_;
}
v___jp_2520_:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; uint8_t v___x_2524_; 
v___x_2522_ = lean_array_fget_borrowed(v___y_2521_, v_mid_2519_);
v___x_2523_ = lean_array_fget_borrowed(v___y_2521_, v_hi_2504_);
lean_inc(v___x_2523_);
lean_inc(v___x_2522_);
v___x_2524_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2516_, v___x_2522_, v___x_2523_);
if (v___x_2524_ == 0)
{
lean_dec(v_mid_2519_);
v___y_2506_ = v___y_2521_;
goto v___jp_2505_;
}
else
{
lean_object* v___x_2525_; 
v___x_2525_ = lean_array_fswap(v___y_2521_, v_mid_2519_, v_hi_2504_);
lean_dec(v_mid_2519_);
v___y_2506_ = v___x_2525_;
goto v___jp_2505_;
}
}
v___jp_2526_:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; 
v___x_2528_ = lean_array_fget_borrowed(v___y_2527_, v_hi_2504_);
v___x_2529_ = lean_array_fget_borrowed(v___y_2527_, v_lo_2503_);
lean_inc(v___x_2529_);
lean_inc(v___x_2528_);
v___x_2530_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2516_, v___x_2528_, v___x_2529_);
if (v___x_2530_ == 0)
{
v___y_2521_ = v___y_2527_;
goto v___jp_2520_;
}
else
{
lean_object* v___x_2531_; 
v___x_2531_ = lean_array_fswap(v___y_2527_, v_lo_2503_, v_hi_2504_);
v___y_2521_ = v___x_2531_;
goto v___jp_2520_;
}
}
}
v___jp_2505_:
{
lean_object* v_pivot_2507_; lean_object* v___x_2508_; lean_object* v_fst_2509_; lean_object* v_snd_2510_; uint8_t v___x_2511_; 
v_pivot_2507_ = lean_array_fget(v___y_2506_, v_hi_2504_);
lean_inc_n(v_lo_2503_, 2);
v___x_2508_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_2504_, v_pivot_2507_, v___y_2506_, v_lo_2503_, v_lo_2503_);
v_fst_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_fst_2509_);
v_snd_2510_ = lean_ctor_get(v___x_2508_, 1);
lean_inc(v_snd_2510_);
lean_dec_ref(v___x_2508_);
v___x_2511_ = lean_nat_dec_le(v_hi_2504_, v_fst_2509_);
if (v___x_2511_ == 0)
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2512_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_2501_, v_snd_2510_, v_lo_2503_, v_fst_2509_);
v___x_2513_ = lean_unsigned_to_nat(1u);
v___x_2514_ = lean_nat_add(v_fst_2509_, v___x_2513_);
lean_dec(v_fst_2509_);
v_as_2502_ = v___x_2512_;
v_lo_2503_ = v___x_2514_;
goto _start;
}
else
{
lean_dec(v_fst_2509_);
lean_dec(v_lo_2503_);
return v_snd_2510_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___boxed(lean_object* v_n_2536_, lean_object* v_as_2537_, lean_object* v_lo_2538_, lean_object* v_hi_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_2536_, v_as_2537_, v_lo_2538_, v_hi_2539_);
lean_dec(v_hi_2539_);
lean_dec(v_n_2536_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(lean_object* v_init_2541_, lean_object* v_x_2542_){
_start:
{
if (lean_obj_tag(v_x_2542_) == 0)
{
lean_object* v_k_2543_; lean_object* v_v_2544_; lean_object* v_l_2545_; lean_object* v_r_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v_k_2543_ = lean_ctor_get(v_x_2542_, 1);
v_v_2544_ = lean_ctor_get(v_x_2542_, 2);
v_l_2545_ = lean_ctor_get(v_x_2542_, 3);
v_r_2546_ = lean_ctor_get(v_x_2542_, 4);
v___x_2547_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_2541_, v_l_2545_);
lean_inc(v_v_2544_);
lean_inc(v_k_2543_);
v___x_2548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2548_, 0, v_k_2543_);
lean_ctor_set(v___x_2548_, 1, v_v_2544_);
v___x_2549_ = lean_array_push(v___x_2547_, v___x_2548_);
v_init_2541_ = v___x_2549_;
v_x_2542_ = v_r_2546_;
goto _start;
}
else
{
return v_init_2541_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25___boxed(lean_object* v_init_2551_, lean_object* v_x_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_2551_, v_x_2552_);
lean_dec(v_x_2552_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(lean_object* v_as_2554_, size_t v_sz_2555_, size_t v_i_2556_, lean_object* v_b_2557_){
_start:
{
uint8_t v___x_2559_; 
v___x_2559_ = lean_usize_dec_lt(v_i_2556_, v_sz_2555_);
if (v___x_2559_ == 0)
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2560_, 0, v_b_2557_);
return v___x_2560_;
}
else
{
lean_object* v_a_2561_; lean_object* v_fst_2562_; lean_object* v_snd_2563_; lean_object* v_found_2564_; size_t v___x_2565_; size_t v___x_2566_; 
v_a_2561_ = lean_array_uget_borrowed(v_as_2554_, v_i_2556_);
v_fst_2562_ = lean_ctor_get(v_a_2561_, 0);
v_snd_2563_ = lean_ctor_get(v_a_2561_, 1);
lean_inc(v_snd_2563_);
lean_inc(v_fst_2562_);
v_found_2564_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2562_, v_snd_2563_, v_b_2557_);
v___x_2565_ = ((size_t)1ULL);
v___x_2566_ = lean_usize_add(v_i_2556_, v___x_2565_);
v_i_2556_ = v___x_2566_;
v_b_2557_ = v_found_2564_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg___boxed(lean_object* v_as_2568_, lean_object* v_sz_2569_, lean_object* v_i_2570_, lean_object* v_b_2571_, lean_object* v___y_2572_){
_start:
{
size_t v_sz_boxed_2573_; size_t v_i_boxed_2574_; lean_object* v_res_2575_; 
v_sz_boxed_2573_ = lean_unbox_usize(v_sz_2569_);
lean_dec(v_sz_2569_);
v_i_boxed_2574_ = lean_unbox_usize(v_i_2570_);
lean_dec(v_i_2570_);
v_res_2575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_2568_, v_sz_boxed_2573_, v_i_boxed_2574_, v_b_2571_);
lean_dec_ref(v_as_2568_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object* v_as_2576_, size_t v_sz_2577_, size_t v_i_2578_, lean_object* v_b_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
uint8_t v___x_2583_; 
v___x_2583_ = lean_usize_dec_lt(v_i_2578_, v_sz_2577_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; 
v___x_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2584_, 0, v_b_2579_);
return v___x_2584_;
}
else
{
lean_object* v_a_2585_; size_t v_sz_2586_; size_t v___x_2587_; lean_object* v___x_2588_; 
v_a_2585_ = lean_array_uget_borrowed(v_as_2576_, v_i_2578_);
v_sz_2586_ = lean_array_size(v_a_2585_);
v___x_2587_ = ((size_t)0ULL);
v___x_2588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_a_2585_, v_sz_2586_, v___x_2587_, v_b_2579_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; size_t v___x_2590_; size_t v___x_2591_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref_known(v___x_2588_, 1);
v___x_2590_ = ((size_t)1ULL);
v___x_2591_ = lean_usize_add(v_i_2578_, v___x_2590_);
v_i_2578_ = v___x_2591_;
v_b_2579_ = v_a_2589_;
goto _start;
}
else
{
return v___x_2588_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object* v_as_2593_, lean_object* v_sz_2594_, lean_object* v_i_2595_, lean_object* v_b_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
size_t v_sz_boxed_2600_; size_t v_i_boxed_2601_; lean_object* v_res_2602_; 
v_sz_boxed_2600_ = lean_unbox_usize(v_sz_2594_);
lean_dec(v_sz_2594_);
v_i_boxed_2601_ = lean_unbox_usize(v_i_2595_);
lean_dec(v_i_2595_);
v_res_2602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_as_2593_, v_sz_boxed_2600_, v_i_boxed_2601_, v_b_2596_, v___y_2597_, v___y_2598_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec_ref(v_as_2593_);
return v_res_2602_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2603_ = lean_box(1);
v___x_2604_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2603_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v___y_2611_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___x_2626_; lean_object* v_env_2627_; lean_object* v___x_2628_; lean_object* v_toEnvExtension_2629_; lean_object* v_asyncMode_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v_a_2636_; lean_object* v_a_2638_; lean_object* v_a_2661_; 
v___x_2626_ = lean_st_ref_get(v___y_2608_);
v_env_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc_ref_n(v_env_2627_, 2);
lean_dec(v___x_2626_);
v___x_2628_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2629_ = lean_ctor_get(v___x_2628_, 0);
v_asyncMode_2630_ = lean_ctor_get(v_toEnvExtension_2629_, 2);
v___x_2631_ = lean_box(1);
v___x_2632_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0, &l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0);
v___x_2633_ = lean_box(0);
v___x_2634_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2631_, v___x_2628_, v_env_2627_, v_asyncMode_2630_, v___x_2633_);
v___x_2635_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v___x_2631_, v___x_2634_);
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2636_);
lean_dec_ref(v___x_2635_);
v_a_2661_ = lean_ctor_get(v_a_2636_, 0);
lean_inc(v_a_2661_);
lean_dec(v_a_2636_);
v_a_2638_ = v_a_2661_;
goto v___jp_2637_;
v___jp_2610_:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = lean_array_to_list(v___y_2611_);
v___x_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
return v___x_2613_;
}
v___jp_2614_:
{
lean_object* v___x_2619_; 
v___x_2619_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v___y_2616_, v___y_2615_, v___y_2617_, v___y_2618_);
lean_dec(v___y_2618_);
lean_dec(v___y_2616_);
v___y_2611_ = v___x_2619_;
goto v___jp_2610_;
}
v___jp_2620_:
{
uint8_t v___x_2625_; 
v___x_2625_ = lean_nat_dec_le(v___y_2624_, v___y_2621_);
if (v___x_2625_ == 0)
{
lean_dec(v___y_2621_);
lean_inc(v___y_2624_);
v___y_2615_ = v___y_2622_;
v___y_2616_ = v___y_2623_;
v___y_2617_ = v___y_2624_;
v___y_2618_ = v___y_2624_;
goto v___jp_2614_;
}
else
{
v___y_2615_ = v___y_2622_;
v___y_2616_ = v___y_2623_;
v___y_2617_ = v___y_2624_;
v___y_2618_ = v___y_2621_;
goto v___jp_2614_;
}
}
v___jp_2637_:
{
lean_object* v___x_2639_; lean_object* v_importedEntries_2640_; size_t v_sz_2641_; size_t v___x_2642_; lean_object* v___x_2643_; 
v___x_2639_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2632_, v_toEnvExtension_2629_, v_env_2627_, v_asyncMode_2630_, v___x_2633_);
v_importedEntries_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc_ref(v_importedEntries_2640_);
lean_dec(v___x_2639_);
v_sz_2641_ = lean_array_size(v_importedEntries_2640_);
v___x_2642_ = ((size_t)0ULL);
v___x_2643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_importedEntries_2640_, v_sz_2641_, v___x_2642_, v_a_2638_, v___y_2607_, v___y_2608_);
lean_dec_ref(v_importedEntries_2640_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v_arr_2647_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v___x_2643_, 1);
v___x_2645_ = lean_unsigned_to_nat(0u);
v___x_2646_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1));
v_arr_2647_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v___x_2646_, v_a_2644_);
lean_dec(v_a_2644_);
v___x_2648_ = lean_array_get_size(v_arr_2647_);
v___x_2649_ = lean_nat_dec_eq(v___x_2648_, v___x_2645_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; 
v___x_2650_ = lean_unsigned_to_nat(1u);
v___x_2651_ = lean_nat_sub(v___x_2648_, v___x_2650_);
v___x_2652_ = lean_nat_dec_le(v___x_2645_, v___x_2651_);
if (v___x_2652_ == 0)
{
lean_inc(v___x_2651_);
v___y_2621_ = v___x_2651_;
v___y_2622_ = v_arr_2647_;
v___y_2623_ = v___x_2648_;
v___y_2624_ = v___x_2651_;
goto v___jp_2620_;
}
else
{
v___y_2621_ = v___x_2651_;
v___y_2622_ = v_arr_2647_;
v___y_2623_ = v___x_2648_;
v___y_2624_ = v___x_2645_;
goto v___jp_2620_;
}
}
else
{
v___y_2611_ = v_arr_2647_;
goto v___jp_2610_;
}
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
v_a_2653_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2643_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2643_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v___y_2662_, v___y_2663_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object* v_t_2666_, lean_object* v_k_2667_, lean_object* v_fallback_2668_){
_start:
{
if (lean_obj_tag(v_t_2666_) == 0)
{
lean_object* v_k_2669_; lean_object* v_v_2670_; lean_object* v_l_2671_; lean_object* v_r_2672_; uint8_t v___x_2673_; 
v_k_2669_ = lean_ctor_get(v_t_2666_, 1);
v_v_2670_ = lean_ctor_get(v_t_2666_, 2);
v_l_2671_ = lean_ctor_get(v_t_2666_, 3);
v_r_2672_ = lean_ctor_get(v_t_2666_, 4);
v___x_2673_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2667_, v_k_2669_);
switch(v___x_2673_)
{
case 0:
{
v_t_2666_ = v_l_2671_;
goto _start;
}
case 1:
{
lean_inc(v_v_2670_);
return v_v_2670_;
}
default: 
{
v_t_2666_ = v_r_2672_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2668_);
return v_fallback_2668_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object* v_t_2676_, lean_object* v_k_2677_, lean_object* v_fallback_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_2676_, v_k_2677_, v_fallback_2678_);
lean_dec(v_fallback_2678_);
lean_dec(v_k_2677_);
lean_dec(v_t_2676_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object* v_as_2680_, size_t v_sz_2681_, size_t v_i_2682_, lean_object* v_b_2683_){
_start:
{
uint8_t v___x_2685_; 
v___x_2685_ = lean_usize_dec_lt(v_i_2682_, v_sz_2681_);
if (v___x_2685_ == 0)
{
lean_object* v___x_2686_; 
v___x_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2686_, 0, v_b_2683_);
return v___x_2686_;
}
else
{
lean_object* v_a_2687_; lean_object* v_fst_2688_; lean_object* v_snd_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; size_t v___x_2694_; size_t v___x_2695_; 
v_a_2687_ = lean_array_uget_borrowed(v_as_2680_, v_i_2682_);
v_fst_2688_ = lean_ctor_get(v_a_2687_, 0);
v_snd_2689_ = lean_ctor_get(v_a_2687_, 1);
v___x_2690_ = l_Lean_NameSet_empty;
v___x_2691_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_2683_, v_snd_2689_, v___x_2690_);
lean_inc(v_fst_2688_);
v___x_2692_ = l_Lean_NameSet_insert(v___x_2691_, v_fst_2688_);
lean_inc(v_snd_2689_);
v___x_2693_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_snd_2689_, v___x_2692_, v_b_2683_);
v___x_2694_ = ((size_t)1ULL);
v___x_2695_ = lean_usize_add(v_i_2682_, v___x_2694_);
v_i_2682_ = v___x_2695_;
v_b_2683_ = v___x_2693_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object* v_as_2697_, lean_object* v_sz_2698_, lean_object* v_i_2699_, lean_object* v_b_2700_, lean_object* v___y_2701_){
_start:
{
size_t v_sz_boxed_2702_; size_t v_i_boxed_2703_; lean_object* v_res_2704_; 
v_sz_boxed_2702_ = lean_unbox_usize(v_sz_2698_);
lean_dec(v_sz_2698_);
v_i_boxed_2703_ = lean_unbox_usize(v_i_2699_);
lean_dec(v_i_2699_);
v_res_2704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_2697_, v_sz_boxed_2702_, v_i_boxed_2703_, v_b_2700_);
lean_dec_ref(v_as_2697_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object* v_as_2705_, size_t v_sz_2706_, size_t v_i_2707_, lean_object* v_b_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
uint8_t v___x_2712_; 
v___x_2712_ = lean_usize_dec_lt(v_i_2707_, v_sz_2706_);
if (v___x_2712_ == 0)
{
lean_object* v___x_2713_; 
v___x_2713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2713_, 0, v_b_2708_);
return v___x_2713_;
}
else
{
lean_object* v_a_2714_; size_t v_sz_2715_; size_t v___x_2716_; lean_object* v___x_2717_; 
v_a_2714_ = lean_array_uget_borrowed(v_as_2705_, v_i_2707_);
v_sz_2715_ = lean_array_size(v_a_2714_);
v___x_2716_ = ((size_t)0ULL);
v___x_2717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_a_2714_, v_sz_2715_, v___x_2716_, v_b_2708_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2718_; size_t v___x_2719_; size_t v___x_2720_; 
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2718_);
lean_dec_ref_known(v___x_2717_, 1);
v___x_2719_ = ((size_t)1ULL);
v___x_2720_ = lean_usize_add(v_i_2707_, v___x_2719_);
v_i_2707_ = v___x_2720_;
v_b_2708_ = v_a_2718_;
goto _start;
}
else
{
return v___x_2717_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object* v_as_2722_, lean_object* v_sz_2723_, lean_object* v_i_2724_, lean_object* v_b_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
size_t v_sz_boxed_2729_; size_t v_i_boxed_2730_; lean_object* v_res_2731_; 
v_sz_boxed_2729_ = lean_unbox_usize(v_sz_2723_);
lean_dec(v_sz_2723_);
v_i_boxed_2730_ = lean_unbox_usize(v_i_2724_);
lean_dec(v_i_2724_);
v_res_2731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v_as_2722_, v_sz_boxed_2729_, v_i_boxed_2730_, v_b_2725_, v___y_2726_, v___y_2727_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec_ref(v_as_2722_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object* v_as_2732_, size_t v_i_2733_, size_t v_stop_2734_, lean_object* v_b_2735_){
_start:
{
uint8_t v___x_2736_; 
v___x_2736_ = lean_usize_dec_eq(v_i_2733_, v_stop_2734_);
if (v___x_2736_ == 0)
{
lean_object* v___x_2737_; lean_object* v_fst_2738_; lean_object* v_snd_2739_; lean_object* v___x_2740_; size_t v___x_2741_; size_t v___x_2742_; 
v___x_2737_ = lean_array_uget_borrowed(v_as_2732_, v_i_2733_);
v_fst_2738_ = lean_ctor_get(v___x_2737_, 0);
v_snd_2739_ = lean_ctor_get(v___x_2737_, 1);
lean_inc(v_snd_2739_);
lean_inc(v_fst_2738_);
v___x_2740_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2738_, v_snd_2739_, v_b_2735_);
v___x_2741_ = ((size_t)1ULL);
v___x_2742_ = lean_usize_add(v_i_2733_, v___x_2741_);
v_i_2733_ = v___x_2742_;
v_b_2735_ = v___x_2740_;
goto _start;
}
else
{
return v_b_2735_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object* v_as_2744_, lean_object* v_i_2745_, lean_object* v_stop_2746_, lean_object* v_b_2747_){
_start:
{
size_t v_i_boxed_2748_; size_t v_stop_boxed_2749_; lean_object* v_res_2750_; 
v_i_boxed_2748_ = lean_unbox_usize(v_i_2745_);
lean_dec(v_i_2745_);
v_stop_boxed_2749_ = lean_unbox_usize(v_stop_2746_);
lean_dec(v_stop_2746_);
v_res_2750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v_as_2744_, v_i_boxed_2748_, v_stop_boxed_2749_, v_b_2747_);
lean_dec_ref(v_as_2744_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object* v_as_2751_, size_t v_i_2752_, size_t v_stop_2753_, lean_object* v_b_2754_){
_start:
{
lean_object* v___y_2756_; uint8_t v___x_2760_; 
v___x_2760_ = lean_usize_dec_eq(v_i_2752_, v_stop_2753_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; uint8_t v___x_2764_; 
v___x_2761_ = lean_array_uget_borrowed(v_as_2751_, v_i_2752_);
v___x_2762_ = lean_unsigned_to_nat(0u);
v___x_2763_ = lean_array_get_size(v___x_2761_);
v___x_2764_ = lean_nat_dec_lt(v___x_2762_, v___x_2763_);
if (v___x_2764_ == 0)
{
v___y_2756_ = v_b_2754_;
goto v___jp_2755_;
}
else
{
uint8_t v___x_2765_; 
v___x_2765_ = lean_nat_dec_le(v___x_2763_, v___x_2763_);
if (v___x_2765_ == 0)
{
if (v___x_2764_ == 0)
{
v___y_2756_ = v_b_2754_;
goto v___jp_2755_;
}
else
{
size_t v___x_2766_; size_t v___x_2767_; lean_object* v___x_2768_; 
v___x_2766_ = ((size_t)0ULL);
v___x_2767_ = lean_usize_of_nat(v___x_2763_);
v___x_2768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_2761_, v___x_2766_, v___x_2767_, v_b_2754_);
v___y_2756_ = v___x_2768_;
goto v___jp_2755_;
}
}
else
{
size_t v___x_2769_; size_t v___x_2770_; lean_object* v___x_2771_; 
v___x_2769_ = ((size_t)0ULL);
v___x_2770_ = lean_usize_of_nat(v___x_2763_);
v___x_2771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_2761_, v___x_2769_, v___x_2770_, v_b_2754_);
v___y_2756_ = v___x_2771_;
goto v___jp_2755_;
}
}
}
else
{
return v_b_2754_;
}
v___jp_2755_:
{
size_t v___x_2757_; size_t v___x_2758_; 
v___x_2757_ = ((size_t)1ULL);
v___x_2758_ = lean_usize_add(v_i_2752_, v___x_2757_);
v_i_2752_ = v___x_2758_;
v_b_2754_ = v___y_2756_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object* v_as_2772_, lean_object* v_i_2773_, lean_object* v_stop_2774_, lean_object* v_b_2775_){
_start:
{
size_t v_i_boxed_2776_; size_t v_stop_boxed_2777_; lean_object* v_res_2778_; 
v_i_boxed_2776_ = lean_unbox_usize(v_i_2773_);
lean_dec(v_i_2773_);
v_stop_boxed_2777_ = lean_unbox_usize(v_stop_2774_);
lean_dec(v_stop_2774_);
v_res_2778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v_as_2772_, v_i_boxed_2776_, v_stop_boxed_2777_, v_b_2775_);
lean_dec_ref(v_as_2772_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object* v___y_2779_){
_start:
{
lean_object* v___x_2781_; lean_object* v_env_2782_; lean_object* v___x_2783_; lean_object* v_ext_2784_; lean_object* v_toEnvExtension_2785_; lean_object* v_asyncMode_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v_categories_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2781_ = lean_st_ref_get(v___y_2779_);
v_env_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc_ref_n(v_env_2782_, 2);
lean_dec(v___x_2781_);
v___x_2783_ = l_Lean_Parser_parserExtension;
v_ext_2784_ = lean_ctor_get(v___x_2783_, 1);
v_toEnvExtension_2785_ = lean_ctor_get(v_ext_2784_, 0);
v_asyncMode_2786_ = lean_ctor_get(v_toEnvExtension_2785_, 2);
v___x_2787_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2788_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2787_, v___x_2783_, v_env_2782_, v_asyncMode_2786_);
v_categories_2789_ = lean_ctor_get(v___x_2788_, 2);
lean_inc_ref(v_categories_2789_);
lean_dec(v___x_2788_);
v___x_2790_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_2791_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_2789_, v___x_2790_);
lean_dec_ref(v_categories_2789_);
if (lean_obj_tag(v___x_2791_) == 1)
{
lean_object* v_val_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2829_; 
v_val_2792_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2794_ = v___x_2791_;
v_isShared_2795_ = v_isSharedCheck_2829_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_val_2792_);
lean_dec(v___x_2791_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2829_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___y_2797_; lean_object* v___x_2806_; lean_object* v_toEnvExtension_2807_; lean_object* v_exportEntriesFn_2808_; lean_object* v_asyncMode_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v_importedEntries_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v_exported_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; uint8_t v___x_2821_; 
v___x_2806_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_2807_ = lean_ctor_get(v___x_2806_, 0);
v_exportEntriesFn_2808_ = lean_ctor_get(v___x_2806_, 4);
v_asyncMode_2809_ = lean_ctor_get(v_toEnvExtension_2807_, 2);
v___x_2810_ = lean_box(1);
v___x_2811_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_2812_ = lean_box(0);
lean_inc_ref_n(v_env_2782_, 2);
v___x_2813_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2811_, v_toEnvExtension_2807_, v_env_2782_, v_asyncMode_2809_, v___x_2812_);
v_importedEntries_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc_ref(v_importedEntries_2814_);
lean_dec(v___x_2813_);
v___x_2815_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2810_, v___x_2806_, v_env_2782_, v_asyncMode_2809_, v___x_2812_);
lean_inc_ref(v_exportEntriesFn_2808_);
v___x_2816_ = lean_apply_2(v_exportEntriesFn_2808_, v_env_2782_, v___x_2815_);
v_exported_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_exported_2817_);
lean_dec_ref(v___x_2816_);
v___x_2818_ = lean_array_push(v_importedEntries_2814_, v_exported_2817_);
v___x_2819_ = lean_unsigned_to_nat(0u);
v___x_2820_ = lean_array_get_size(v___x_2818_);
v___x_2821_ = lean_nat_dec_lt(v___x_2819_, v___x_2820_);
if (v___x_2821_ == 0)
{
lean_dec_ref(v___x_2818_);
v___y_2797_ = v___x_2810_;
goto v___jp_2796_;
}
else
{
uint8_t v___x_2822_; 
v___x_2822_ = lean_nat_dec_le(v___x_2820_, v___x_2820_);
if (v___x_2822_ == 0)
{
if (v___x_2821_ == 0)
{
lean_dec_ref(v___x_2818_);
v___y_2797_ = v___x_2810_;
goto v___jp_2796_;
}
else
{
size_t v___x_2823_; size_t v___x_2824_; lean_object* v___x_2825_; 
v___x_2823_ = ((size_t)0ULL);
v___x_2824_ = lean_usize_of_nat(v___x_2820_);
v___x_2825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_2818_, v___x_2823_, v___x_2824_, v___x_2810_);
lean_dec_ref(v___x_2818_);
v___y_2797_ = v___x_2825_;
goto v___jp_2796_;
}
}
else
{
size_t v___x_2826_; size_t v___x_2827_; lean_object* v___x_2828_; 
v___x_2826_ = ((size_t)0ULL);
v___x_2827_ = lean_usize_of_nat(v___x_2820_);
v___x_2828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_2818_, v___x_2826_, v___x_2827_, v___x_2810_);
lean_dec_ref(v___x_2818_);
v___y_2797_ = v___x_2828_;
goto v___jp_2796_;
}
}
v___jp_2796_:
{
lean_object* v_tables_2798_; lean_object* v_leadingTable_2799_; lean_object* v_trailingTable_2800_; lean_object* v_firstTokens_2801_; lean_object* v_firstTokens_2802_; lean_object* v___x_2804_; 
v_tables_2798_ = lean_ctor_get(v_val_2792_, 2);
v_leadingTable_2799_ = lean_ctor_get(v_tables_2798_, 0);
v_trailingTable_2800_ = lean_ctor_get(v_tables_2798_, 2);
lean_inc(v_trailingTable_2800_);
lean_inc(v_leadingTable_2799_);
lean_inc(v_val_2792_);
v_firstTokens_2801_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2792_, v_leadingTable_2799_, v___y_2797_);
v_firstTokens_2802_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2792_, v_trailingTable_2800_, v_firstTokens_2801_);
if (v_isShared_2795_ == 0)
{
lean_ctor_set_tag(v___x_2794_, 0);
lean_ctor_set(v___x_2794_, 0, v_firstTokens_2802_);
v___x_2804_ = v___x_2794_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_firstTokens_2802_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
else
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
lean_dec(v___x_2791_);
lean_dec_ref(v_env_2782_);
v___x_2830_ = lean_box(1);
v___x_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
return v___x_2831_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_2832_);
lean_dec(v___y_2832_);
return v_res_2834_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0(void){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = lean_box(1);
v___x_2836_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2835_);
return v___x_2836_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2(void){
_start:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2838_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1));
v___x_2839_ = l_Lean_stringToMessageData(v___x_2838_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object* v_a_2840_, lean_object* v_a_2841_){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v_env_2846_; lean_object* v_env_2847_; lean_object* v_env_2848_; lean_object* v___x_2849_; lean_object* v_toEnvExtension_2850_; lean_object* v_exportEntriesFn_2851_; lean_object* v_asyncMode_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v_importedEntries_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2909_; 
v___x_2843_ = lean_st_ref_get(v_a_2841_);
v___x_2844_ = lean_st_ref_get(v_a_2841_);
v___x_2845_ = lean_st_ref_get(v_a_2841_);
v_env_2846_ = lean_ctor_get(v___x_2843_, 0);
lean_inc_ref(v_env_2846_);
lean_dec(v___x_2843_);
v_env_2847_ = lean_ctor_get(v___x_2844_, 0);
lean_inc_ref(v_env_2847_);
lean_dec(v___x_2844_);
v_env_2848_ = lean_ctor_get(v___x_2845_, 0);
lean_inc_ref(v_env_2848_);
lean_dec(v___x_2845_);
v___x_2849_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_2850_ = lean_ctor_get(v___x_2849_, 0);
v_exportEntriesFn_2851_ = lean_ctor_get(v___x_2849_, 4);
v_asyncMode_2852_ = lean_ctor_get(v_toEnvExtension_2850_, 2);
v___x_2853_ = lean_box(1);
v___x_2854_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_2855_ = lean_box(0);
v___x_2856_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2854_, v_toEnvExtension_2850_, v_env_2846_, v_asyncMode_2852_, v___x_2855_);
v_importedEntries_2857_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2909_ == 0)
{
lean_object* v_unused_2910_; 
v_unused_2910_ = lean_ctor_get(v___x_2856_, 1);
lean_dec(v_unused_2910_);
v___x_2859_ = v___x_2856_;
v_isShared_2860_ = v_isSharedCheck_2909_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_importedEntries_2857_);
lean_dec(v___x_2856_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2909_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v_exported_2863_; lean_object* v___x_2864_; size_t v_sz_2865_; size_t v___x_2866_; lean_object* v___x_2867_; 
v___x_2861_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2853_, v___x_2849_, v_env_2848_, v_asyncMode_2852_, v___x_2855_);
lean_inc_ref(v_exportEntriesFn_2851_);
v___x_2862_ = lean_apply_2(v_exportEntriesFn_2851_, v_env_2847_, v___x_2861_);
v_exported_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_exported_2863_);
lean_dec_ref(v___x_2862_);
v___x_2864_ = lean_array_push(v_importedEntries_2857_, v_exported_2863_);
v_sz_2865_ = lean_array_size(v___x_2864_);
v___x_2866_ = ((size_t)0ULL);
v___x_2867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v___x_2864_, v_sz_2865_, v___x_2866_, v___x_2853_, v_a_2840_, v_a_2841_);
lean_dec_ref(v___x_2864_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; lean_object* v___x_2869_; lean_object* v_a_2870_; lean_object* v___x_2871_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_a_2868_);
lean_dec_ref_known(v___x_2867_, 1);
v___x_2869_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v_a_2841_);
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref(v___x_2869_);
v___x_2871_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2871_, 1);
v___x_2873_ = lean_box(0);
v___x_2874_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_2870_, v_a_2868_, v_a_2872_, v___x_2873_, v_a_2840_, v_a_2841_);
lean_dec(v_a_2868_);
lean_dec(v_a_2870_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2880_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2874_, 1);
v___x_2876_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2);
v___x_2877_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2878_ = l_Lean_MessageData_joinSep(v_a_2875_, v___x_2877_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set_tag(v___x_2859_, 7);
lean_ctor_set(v___x_2859_, 1, v___x_2878_);
lean_ctor_set(v___x_2859_, 0, v___x_2877_);
v___x_2880_ = v___x_2859_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2877_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v___x_2878_);
v___x_2880_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2881_ = l_Lean_MessageData_nestD(v___x_2880_);
v___x_2882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2876_);
lean_ctor_set(v___x_2882_, 1, v___x_2881_);
v___x_2883_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v___x_2882_, v_a_2840_, v_a_2841_);
return v___x_2883_;
}
}
else
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
lean_del_object(v___x_2859_);
v_a_2885_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2887_ = v___x_2874_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2874_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2885_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
lean_dec(v_a_2870_);
lean_dec(v_a_2868_);
lean_del_object(v___x_2859_);
v_a_2893_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2871_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2871_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_del_object(v___x_2859_);
v_a_2901_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2867_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2867_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_2911_, v_a_2912_);
lean_dec(v_a_2912_);
lean_dec_ref(v_a_2911_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object* v___stx_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_){
_start:
{
lean_object* v___x_2919_; 
v___x_2919_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_2916_, v_a_2917_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object* v___stx_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags(v___stx_2920_, v_a_2921_, v_a_2922_);
lean_dec(v_a_2922_);
lean_dec_ref(v_a_2921_);
lean_dec(v___stx_2920_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object* v_00_u03b4_2925_, lean_object* v_t_2926_, lean_object* v_k_2927_, lean_object* v_fallback_2928_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_2926_, v_k_2927_, v_fallback_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object* v_00_u03b4_2930_, lean_object* v_t_2931_, lean_object* v_k_2932_, lean_object* v_fallback_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(v_00_u03b4_2930_, v_t_2931_, v_k_2932_, v_fallback_2933_);
lean_dec(v_fallback_2933_);
lean_dec(v_k_2932_);
lean_dec(v_t_2931_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object* v_as_2935_, size_t v_sz_2936_, size_t v_i_2937_, lean_object* v_b_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_2935_, v_sz_2936_, v_i_2937_, v_b_2938_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object* v_as_2943_, lean_object* v_sz_2944_, lean_object* v_i_2945_, lean_object* v_b_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
size_t v_sz_boxed_2950_; size_t v_i_boxed_2951_; lean_object* v_res_2952_; 
v_sz_boxed_2950_ = lean_unbox_usize(v_sz_2944_);
lean_dec(v_sz_2944_);
v_i_boxed_2951_ = lean_unbox_usize(v_i_2945_);
lean_dec(v_i_2945_);
v_res_2952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(v_as_2943_, v_sz_boxed_2950_, v_i_boxed_2951_, v_b_2946_, v___y_2947_, v___y_2948_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec_ref(v_as_2943_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_2954_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(v___y_2957_, v___y_2958_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object* v_val_2961_, lean_object* v___x_2962_, lean_object* v___x_2963_, lean_object* v_inst_2964_, lean_object* v_R_2965_, lean_object* v_a_2966_, lean_object* v_b_2967_){
_start:
{
lean_object* v___x_2968_; 
v___x_2968_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2961_, v___x_2962_, v___x_2963_, v_a_2966_, v_b_2967_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object* v_val_2969_, lean_object* v___x_2970_, lean_object* v___x_2971_, lean_object* v_inst_2972_, lean_object* v_R_2973_, lean_object* v_a_2974_, lean_object* v_b_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(v_val_2969_, v___x_2970_, v___x_2971_, v_inst_2972_, v_R_2973_, v_a_2974_, v_b_2975_);
lean_dec_ref(v___x_2970_);
lean_dec_ref(v_val_2969_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object* v_init_2977_, lean_object* v_t_2978_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_2977_, v_t_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object* v_n_2980_, lean_object* v_as_2981_, lean_object* v_lo_2982_, lean_object* v_hi_2983_, lean_object* v_w_2984_, lean_object* v_hlo_2985_, lean_object* v_hhi_2986_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_2980_, v_as_2981_, v_lo_2982_, v_hi_2983_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object* v_n_2988_, lean_object* v_as_2989_, lean_object* v_lo_2990_, lean_object* v_hi_2991_, lean_object* v_w_2992_, lean_object* v_hlo_2993_, lean_object* v_hhi_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(v_n_2988_, v_as_2989_, v_lo_2990_, v_hi_2991_, v_w_2992_, v_hlo_2993_, v_hhi_2994_);
lean_dec(v_hi_2991_);
lean_dec(v_n_2988_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object* v_00_u03b2_2996_, lean_object* v_x_2997_, lean_object* v_x_2998_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_2997_, v_x_2998_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3000_, lean_object* v_x_3001_, lean_object* v_x_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(v_00_u03b2_3000_, v_x_3001_, v_x_3002_);
lean_dec(v_x_3002_);
lean_dec_ref(v_x_3001_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object* v_tac_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_3004_, v___y_3006_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object* v_tac_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(v_tac_3009_, v___y_3010_, v___y_3011_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object* v_00_u03b4_3014_, lean_object* v_t_3015_, lean_object* v_k_3016_){
_start:
{
lean_object* v___x_3017_; 
v___x_3017_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_3015_, v_k_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___boxed(lean_object* v_00_u03b4_3018_, lean_object* v_t_3019_, lean_object* v_k_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(v_00_u03b4_3018_, v_t_3019_, v_k_3020_);
lean_dec(v_k_3020_);
lean_dec(v_t_3019_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object* v_00_u03b2_3022_, lean_object* v_x_3023_, lean_object* v_x_3024_){
_start:
{
lean_object* v___x_3025_; 
v___x_3025_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_3023_, v_x_3024_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object* v_00_u03b2_3026_, lean_object* v_x_3027_, lean_object* v_x_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(v_00_u03b2_3026_, v_x_3027_, v_x_3028_);
lean_dec(v_x_3028_);
lean_dec_ref(v_x_3027_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(lean_object* v_n_3030_, lean_object* v_lo_3031_, lean_object* v_hi_3032_, lean_object* v_hhi_3033_, lean_object* v_pivot_3034_, lean_object* v_as_3035_, lean_object* v_i_3036_, lean_object* v_k_3037_, lean_object* v_ilo_3038_, lean_object* v_ik_3039_, lean_object* v_w_3040_){
_start:
{
lean_object* v___x_3041_; 
v___x_3041_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_3032_, v_pivot_3034_, v_as_3035_, v_i_3036_, v_k_3037_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___boxed(lean_object* v_n_3042_, lean_object* v_lo_3043_, lean_object* v_hi_3044_, lean_object* v_hhi_3045_, lean_object* v_pivot_3046_, lean_object* v_as_3047_, lean_object* v_i_3048_, lean_object* v_k_3049_, lean_object* v_ilo_3050_, lean_object* v_ik_3051_, lean_object* v_w_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(v_n_3042_, v_lo_3043_, v_hi_3044_, v_hhi_3045_, v_pivot_3046_, v_as_3047_, v_i_3048_, v_k_3049_, v_ilo_3050_, v_ik_3051_, v_w_3052_);
lean_dec(v_hi_3044_);
lean_dec(v_lo_3043_);
lean_dec(v_n_3042_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(lean_object* v_as_3054_, size_t v_sz_3055_, size_t v_i_3056_, lean_object* v_b_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_){
_start:
{
lean_object* v___x_3061_; 
v___x_3061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_3054_, v_sz_3055_, v_i_3056_, v_b_3057_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___boxed(lean_object* v_as_3062_, lean_object* v_sz_3063_, lean_object* v_i_3064_, lean_object* v_b_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
size_t v_sz_boxed_3069_; size_t v_i_boxed_3070_; lean_object* v_res_3071_; 
v_sz_boxed_3069_ = lean_unbox_usize(v_sz_3063_);
lean_dec(v_sz_3063_);
v_i_boxed_3070_ = lean_unbox_usize(v_i_3064_);
lean_dec(v_i_3064_);
v_res_3071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(v_as_3062_, v_sz_boxed_3069_, v_i_boxed_3070_, v_b_3065_, v___y_3066_, v___y_3067_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec_ref(v_as_3062_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object* v_init_3072_, lean_object* v_t_3073_){
_start:
{
lean_object* v___x_3074_; 
v___x_3074_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_3072_, v_t_3073_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object* v_init_3075_, lean_object* v_t_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(v_init_3075_, v_t_3076_);
lean_dec(v_t_3076_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object* v_n_3078_, lean_object* v_as_3079_, lean_object* v_lo_3080_, lean_object* v_hi_3081_, lean_object* v_w_3082_, lean_object* v_hlo_3083_, lean_object* v_hhi_3084_){
_start:
{
lean_object* v___x_3085_; 
v___x_3085_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_3078_, v_as_3079_, v_lo_3080_, v_hi_3081_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object* v_n_3086_, lean_object* v_as_3087_, lean_object* v_lo_3088_, lean_object* v_hi_3089_, lean_object* v_w_3090_, lean_object* v_hlo_3091_, lean_object* v_hhi_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(v_n_3086_, v_as_3087_, v_lo_3088_, v_hi_3089_, v_w_3090_, v_hlo_3091_, v_hhi_3092_);
lean_dec(v_hi_3089_);
lean_dec(v_n_3086_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object* v_init_3094_, lean_object* v_x_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v___x_3099_; 
v___x_3099_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_3094_, v_x_3095_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object* v_init_3100_, lean_object* v_x_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(v_init_3100_, v_x_3101_, v___y_3102_, v___y_3103_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_3106_, lean_object* v_x_3107_, size_t v_x_3108_, lean_object* v_x_3109_){
_start:
{
lean_object* v___x_3110_; 
v___x_3110_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3107_, v_x_3108_, v_x_3109_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3111_, lean_object* v_x_3112_, lean_object* v_x_3113_, lean_object* v_x_3114_){
_start:
{
size_t v_x_19380__boxed_3115_; lean_object* v_res_3116_; 
v_x_19380__boxed_3115_ = lean_unbox_usize(v_x_3113_);
lean_dec(v_x_3113_);
v_res_3116_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(v_00_u03b2_3111_, v_x_3112_, v_x_19380__boxed_3115_, v_x_3114_);
lean_dec(v_x_3114_);
lean_dec_ref(v_x_3112_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object* v_as_3117_, lean_object* v_k_3118_, lean_object* v_x_3119_, lean_object* v_x_3120_, lean_object* v_x_3121_){
_start:
{
lean_object* v___x_3122_; 
v___x_3122_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_3117_, v_k_3118_, v_x_3119_, v_x_3120_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object* v_as_3123_, lean_object* v_k_3124_, lean_object* v_x_3125_, lean_object* v_x_3126_, lean_object* v_x_3127_){
_start:
{
lean_object* v_res_3128_; 
v_res_3128_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(v_as_3123_, v_k_3124_, v_x_3125_, v_x_3126_, v_x_3127_);
lean_dec_ref(v_k_3124_);
lean_dec_ref(v_as_3123_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(lean_object* v_00_u03b2_3129_, lean_object* v_m_3130_, lean_object* v_a_3131_){
_start:
{
lean_object* v___x_3132_; 
v___x_3132_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_3130_, v_a_3131_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___boxed(lean_object* v_00_u03b2_3133_, lean_object* v_m_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(v_00_u03b2_3133_, v_m_3134_, v_a_3135_);
lean_dec(v_a_3135_);
lean_dec_ref(v_m_3134_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(lean_object* v_n_3137_, lean_object* v_lo_3138_, lean_object* v_hi_3139_, lean_object* v_hhi_3140_, lean_object* v_pivot_3141_, lean_object* v_as_3142_, lean_object* v_i_3143_, lean_object* v_k_3144_, lean_object* v_ilo_3145_, lean_object* v_ik_3146_, lean_object* v_w_3147_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_3139_, v_pivot_3141_, v_as_3142_, v_i_3143_, v_k_3144_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___boxed(lean_object* v_n_3149_, lean_object* v_lo_3150_, lean_object* v_hi_3151_, lean_object* v_hhi_3152_, lean_object* v_pivot_3153_, lean_object* v_as_3154_, lean_object* v_i_3155_, lean_object* v_k_3156_, lean_object* v_ilo_3157_, lean_object* v_ik_3158_, lean_object* v_w_3159_){
_start:
{
lean_object* v_res_3160_; 
v_res_3160_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(v_n_3149_, v_lo_3150_, v_hi_3151_, v_hhi_3152_, v_pivot_3153_, v_as_3154_, v_i_3155_, v_k_3156_, v_ilo_3157_, v_ik_3158_, v_w_3159_);
lean_dec(v_hi_3151_);
lean_dec(v_lo_3150_);
lean_dec(v_n_3149_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_3161_, lean_object* v_keys_3162_, lean_object* v_vals_3163_, lean_object* v_heq_3164_, lean_object* v_i_3165_, lean_object* v_k_3166_){
_start:
{
lean_object* v___x_3167_; 
v___x_3167_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_3162_, v_vals_3163_, v_i_3165_, v_k_3166_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object* v_00_u03b2_3168_, lean_object* v_keys_3169_, lean_object* v_vals_3170_, lean_object* v_heq_3171_, lean_object* v_i_3172_, lean_object* v_k_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(v_00_u03b2_3168_, v_keys_3169_, v_vals_3170_, v_heq_3171_, v_i_3172_, v_k_3173_);
lean_dec(v_k_3173_);
lean_dec_ref(v_vals_3170_);
lean_dec_ref(v_keys_3169_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(lean_object* v_00_u03b2_3175_, lean_object* v_m_3176_, lean_object* v_query_3177_){
_start:
{
lean_object* v___x_3178_; 
v___x_3178_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_m_3176_, v_query_3177_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___boxed(lean_object* v_00_u03b2_3179_, lean_object* v_m_3180_, lean_object* v_query_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(v_00_u03b2_3179_, v_m_3180_, v_query_3181_);
lean_dec(v_query_3181_);
lean_dec_ref(v_m_3180_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32(lean_object* v_00_u03b2_3183_, lean_object* v_m_3184_, lean_object* v_query_3185_){
_start:
{
lean_object* v___x_3186_; 
v___x_3186_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32___redArg(v_m_3184_, v_query_3185_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32___boxed(lean_object* v_00_u03b2_3187_, lean_object* v_m_3188_, lean_object* v_query_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32(v_00_u03b2_3187_, v_m_3188_, v_query_3189_);
lean_dec(v_query_3189_);
lean_dec_ref(v_m_3188_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32_spec__36(lean_object* v_00_u03b2_3191_, lean_object* v_m_3192_, lean_object* v_query_3193_, lean_object* v_x_3194_, lean_object* v_x_3195_, lean_object* v_x_3196_, lean_object* v_x_3197_){
_start:
{
lean_object* v___x_3198_; 
v___x_3198_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32_spec__36___redArg(v_m_3192_, v_query_3193_, v_x_3194_, v_x_3195_, v_x_3196_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32_spec__36___boxed(lean_object* v_00_u03b2_3199_, lean_object* v_m_3200_, lean_object* v_query_3201_, lean_object* v_x_3202_, lean_object* v_x_3203_, lean_object* v_x_3204_, lean_object* v_x_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22_spec__32_spec__36(v_00_u03b2_3199_, v_m_3200_, v_query_3201_, v_x_3202_, v_x_3203_, v_x_3204_, v_x_3205_);
lean_dec(v_query_3201_);
lean_dec_ref(v_m_3200_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1(){
_start:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3221_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3222_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1));
v___x_3223_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3224_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed), 4, 0);
v___x_3225_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3221_, v___x_3222_, v___x_3223_, v___x_3224_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object* v_a_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3(){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3230_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3231_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0));
v___x_3232_ = l_Lean_addBuiltinDocString(v___x_3230_, v___x_3231_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object* v_a_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5(){
_start:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3261_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3262_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6));
v___x_3263_ = l_Lean_addBuiltinDeclarationRanges(v___x_3261_, v___x_3262_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object* v_a_3264_){
_start:
{
lean_object* v_res_3265_; 
v_res_3265_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
return v_res_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object* v_env_3266_, lean_object* v___x_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, uint8_t v_includeUnnamed_3270_, lean_object* v_x_3271_, lean_object* v_____s_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v_fst_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3333_; 
v_fst_3278_ = lean_ctor_get(v_x_3271_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v_x_3271_);
if (v_isSharedCheck_3333_ == 0)
{
lean_object* v_unused_3334_; 
v_unused_3334_ = lean_ctor_get(v_x_3271_, 1);
lean_dec(v_unused_3334_);
v___x_3280_ = v_x_3271_;
v_isShared_3281_ = v_isSharedCheck_3333_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_fst_3278_);
lean_dec(v_x_3271_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3333_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v_userName_3283_; lean_object* v___y_3284_; lean_object* v___x_3318_; 
lean_inc(v_fst_3278_);
lean_inc_ref(v_env_3266_);
v___x_3318_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_3266_, v_fst_3278_);
if (lean_obj_tag(v___x_3318_) == 1)
{
lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3326_; 
lean_del_object(v___x_3280_);
lean_dec(v_fst_3278_);
lean_dec(v___x_3267_);
lean_dec_ref(v_env_3266_);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3326_ == 0)
{
lean_object* v_unused_3327_; 
v_unused_3327_ = lean_ctor_get(v___x_3318_, 0);
lean_dec(v_unused_3327_);
v___x_3320_ = v___x_3318_;
v_isShared_3321_ = v_isSharedCheck_3326_;
goto v_resetjp_3319_;
}
else
{
lean_dec(v___x_3318_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3326_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
lean_ctor_set(v___x_3320_, 0, v_____s_3272_);
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_____s_3272_);
v___x_3323_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
lean_object* v___x_3324_; 
v___x_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
return v___x_3324_;
}
}
}
else
{
lean_object* v___x_3328_; 
lean_dec(v___x_3318_);
v___x_3328_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_a_3269_, v_fst_3278_);
if (lean_obj_tag(v___x_3328_) == 1)
{
lean_object* v_val_3329_; 
v_val_3329_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_val_3329_);
lean_dec_ref_known(v___x_3328_, 1);
v_userName_3283_ = v_val_3329_;
v___y_3284_ = v___y_3275_;
goto v___jp_3282_;
}
else
{
lean_dec(v___x_3328_);
if (v_includeUnnamed_3270_ == 0)
{
lean_object* v___x_3330_; lean_object* v___x_3331_; 
lean_del_object(v___x_3280_);
lean_dec(v_fst_3278_);
lean_dec(v___x_3267_);
lean_dec_ref(v_env_3266_);
v___x_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3330_, 0, v_____s_3272_);
v___x_3331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
return v___x_3331_;
}
else
{
lean_object* v___x_3332_; 
lean_inc(v_fst_3278_);
v___x_3332_ = l_Lean_Name_toString(v_fst_3278_, v_includeUnnamed_3270_);
v_userName_3283_ = v___x_3332_;
v___y_3284_ = v___y_3275_;
goto v___jp_3282_;
}
}
}
v___jp_3282_:
{
uint8_t v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
v___x_3285_ = 1;
v___x_3286_ = l_Lean_Options_empty;
v___x_3287_ = lean_box(0);
lean_inc(v_fst_3278_);
lean_inc_ref(v_env_3266_);
v___x_3288_ = l_Lean_findDocString_x3f(v_env_3266_, v_fst_3278_, v___x_3285_, v___x_3286_, v___x_3267_, v___x_3287_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3302_; 
lean_del_object(v___x_3280_);
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3291_ = v___x_3288_;
v_isShared_3292_ = v_isSharedCheck_3302_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3288_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3302_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3300_; 
v___x_3293_ = l_Lean_NameSet_empty;
v___x_3294_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_a_3268_, v_fst_3278_, v___x_3293_);
lean_inc(v_fst_3278_);
v___x_3295_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_3266_, v_fst_3278_);
v___x_3296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3296_, 0, v_fst_3278_);
lean_ctor_set(v___x_3296_, 1, v_userName_3283_);
lean_ctor_set(v___x_3296_, 2, v___x_3294_);
lean_ctor_set(v___x_3296_, 3, v_a_3289_);
lean_ctor_set(v___x_3296_, 4, v___x_3295_);
v___x_3297_ = lean_array_push(v_____s_3272_, v___x_3296_);
v___x_3298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 0, v___x_3298_);
v___x_3300_ = v___x_3291_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3298_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3317_; 
lean_dec_ref(v_userName_3283_);
lean_dec(v_fst_3278_);
lean_dec_ref(v_____s_3272_);
lean_dec_ref(v_env_3266_);
v_a_3303_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3305_ = v___x_3288_;
v_isShared_3306_ = v_isSharedCheck_3317_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3288_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3317_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v_ref_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3312_; 
v_ref_3307_ = lean_ctor_get(v___y_3284_, 5);
v___x_3308_ = lean_io_error_to_string(v_a_3303_);
v___x_3309_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3308_);
v___x_3310_ = l_Lean_MessageData_ofFormat(v___x_3309_);
lean_inc(v_ref_3307_);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 1, v___x_3310_);
lean_ctor_set(v___x_3280_, 0, v_ref_3307_);
v___x_3312_ = v___x_3280_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_ref_3307_);
lean_ctor_set(v_reuseFailAlloc_3316_, 1, v___x_3310_);
v___x_3312_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
lean_object* v___x_3314_; 
if (v_isShared_3306_ == 0)
{
lean_ctor_set(v___x_3305_, 0, v___x_3312_);
v___x_3314_ = v___x_3305_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3312_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object* v_env_3335_, lean_object* v___x_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_includeUnnamed_3339_, lean_object* v_x_3340_, lean_object* v_____s_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
uint8_t v_includeUnnamed_boxed_3347_; lean_object* v_res_3348_; 
v_includeUnnamed_boxed_3347_ = lean_unbox(v_includeUnnamed_3339_);
v_res_3348_ = l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(v_env_3335_, v___x_3336_, v_a_3337_, v_a_3338_, v_includeUnnamed_boxed_3347_, v_x_3340_, v_____s_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
lean_dec(v___y_3343_);
lean_dec_ref(v___y_3342_);
lean_dec(v_a_3338_);
lean_dec(v_a_3337_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object* v_as_3349_, size_t v_sz_3350_, size_t v_i_3351_, lean_object* v_b_3352_){
_start:
{
uint8_t v___x_3354_; 
v___x_3354_ = lean_usize_dec_lt(v_i_3351_, v_sz_3350_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; 
v___x_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3355_, 0, v_b_3352_);
return v___x_3355_;
}
else
{
lean_object* v_a_3356_; lean_object* v_fst_3357_; lean_object* v_snd_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; size_t v___x_3363_; size_t v___x_3364_; 
v_a_3356_ = lean_array_uget_borrowed(v_as_3349_, v_i_3351_);
v_fst_3357_ = lean_ctor_get(v_a_3356_, 0);
v_snd_3358_ = lean_ctor_get(v_a_3356_, 1);
v___x_3359_ = l_Lean_NameSet_empty;
v___x_3360_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_3352_, v_fst_3357_, v___x_3359_);
lean_inc(v_snd_3358_);
v___x_3361_ = l_Lean_NameSet_insert(v___x_3360_, v_snd_3358_);
lean_inc(v_fst_3357_);
v___x_3362_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3357_, v___x_3361_, v_b_3352_);
v___x_3363_ = ((size_t)1ULL);
v___x_3364_ = lean_usize_add(v_i_3351_, v___x_3363_);
v_i_3351_ = v___x_3364_;
v_b_3352_ = v___x_3362_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object* v_as_3366_, lean_object* v_sz_3367_, lean_object* v_i_3368_, lean_object* v_b_3369_, lean_object* v___y_3370_){
_start:
{
size_t v_sz_boxed_3371_; size_t v_i_boxed_3372_; lean_object* v_res_3373_; 
v_sz_boxed_3371_ = lean_unbox_usize(v_sz_3367_);
lean_dec(v_sz_3367_);
v_i_boxed_3372_ = lean_unbox_usize(v_i_3368_);
lean_dec(v_i_3368_);
v_res_3373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_3366_, v_sz_boxed_3371_, v_i_boxed_3372_, v_b_3369_);
lean_dec_ref(v_as_3366_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object* v_as_3374_, size_t v_sz_3375_, size_t v_i_3376_, lean_object* v_b_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
uint8_t v___x_3383_; 
v___x_3383_ = lean_usize_dec_lt(v_i_3376_, v_sz_3375_);
if (v___x_3383_ == 0)
{
lean_object* v___x_3384_; 
v___x_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3384_, 0, v_b_3377_);
return v___x_3384_;
}
else
{
lean_object* v_a_3385_; size_t v_sz_3386_; size_t v___x_3387_; lean_object* v___x_3388_; 
v_a_3385_ = lean_array_uget_borrowed(v_as_3374_, v_i_3376_);
v_sz_3386_ = lean_array_size(v_a_3385_);
v___x_3387_ = ((size_t)0ULL);
v___x_3388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_a_3385_, v_sz_3386_, v___x_3387_, v_b_3377_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; size_t v___x_3390_; size_t v___x_3391_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_a_3389_);
lean_dec_ref_known(v___x_3388_, 1);
v___x_3390_ = ((size_t)1ULL);
v___x_3391_ = lean_usize_add(v_i_3376_, v___x_3390_);
v_i_3376_ = v___x_3391_;
v_b_3377_ = v_a_3389_;
goto _start;
}
else
{
return v___x_3388_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object* v_as_3393_, lean_object* v_sz_3394_, lean_object* v_i_3395_, lean_object* v_b_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
size_t v_sz_boxed_3402_; size_t v_i_boxed_3403_; lean_object* v_res_3404_; 
v_sz_boxed_3402_ = lean_unbox_usize(v_sz_3394_);
lean_dec(v_sz_3394_);
v_i_boxed_3403_ = lean_unbox_usize(v_i_3395_);
lean_dec(v_i_3395_);
v_res_3404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v_as_3393_, v_sz_boxed_3402_, v_i_boxed_3403_, v_b_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec_ref(v_as_3393_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object* v_f_3405_, lean_object* v_keys_3406_, lean_object* v_vals_3407_, lean_object* v_i_3408_, lean_object* v_acc_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
lean_object* v___x_3415_; uint8_t v___x_3416_; 
v___x_3415_ = lean_array_get_size(v_keys_3406_);
v___x_3416_ = lean_nat_dec_lt(v_i_3408_, v___x_3415_);
if (v___x_3416_ == 0)
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
lean_dec(v_i_3408_);
lean_dec_ref(v_f_3405_);
v___x_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3417_, 0, v_acc_3409_);
v___x_3418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3417_);
return v___x_3418_;
}
else
{
lean_object* v_k_3419_; lean_object* v_v_3420_; lean_object* v___x_3421_; 
v_k_3419_ = lean_array_fget_borrowed(v_keys_3406_, v_i_3408_);
v_v_3420_ = lean_array_fget_borrowed(v_vals_3407_, v_i_3408_);
lean_inc_ref(v_f_3405_);
lean_inc(v___y_3413_);
lean_inc_ref(v___y_3412_);
lean_inc(v___y_3411_);
lean_inc_ref(v___y_3410_);
lean_inc(v_v_3420_);
lean_inc(v_k_3419_);
v___x_3421_ = lean_apply_8(v_f_3405_, v_acc_3409_, v_k_3419_, v_v_3420_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, lean_box(0));
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_a_3422_; 
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3422_);
if (lean_obj_tag(v_a_3422_) == 0)
{
lean_dec_ref_known(v_a_3422_, 1);
lean_dec(v_i_3408_);
lean_dec_ref(v_f_3405_);
return v___x_3421_;
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
lean_dec_ref_known(v___x_3421_, 1);
v_a_3423_ = lean_ctor_get(v_a_3422_, 0);
lean_inc(v_a_3423_);
lean_dec_ref_known(v_a_3422_, 1);
v___x_3424_ = lean_unsigned_to_nat(1u);
v___x_3425_ = lean_nat_add(v_i_3408_, v___x_3424_);
lean_dec(v_i_3408_);
v_i_3408_ = v___x_3425_;
v_acc_3409_ = v_a_3423_;
goto _start;
}
}
else
{
lean_dec(v_i_3408_);
lean_dec_ref(v_f_3405_);
return v___x_3421_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_f_3427_, lean_object* v_keys_3428_, lean_object* v_vals_3429_, lean_object* v_i_3430_, lean_object* v_acc_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3427_, v_keys_3428_, v_vals_3429_, v_i_3430_, v_acc_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec_ref(v_vals_3429_);
lean_dec_ref(v_keys_3428_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object* v_f_3438_, lean_object* v_x_3439_, lean_object* v_x_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
if (lean_obj_tag(v_x_3439_) == 0)
{
lean_object* v_es_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3468_; 
v_es_3446_ = lean_ctor_get(v_x_3439_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v_x_3439_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3448_ = v_x_3439_;
v_isShared_3449_ = v_isSharedCheck_3468_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_es_3446_);
lean_dec(v_x_3439_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3468_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; uint8_t v___x_3452_; 
v___x_3450_ = lean_unsigned_to_nat(0u);
v___x_3451_ = lean_array_get_size(v_es_3446_);
v___x_3452_ = lean_nat_dec_lt(v___x_3450_, v___x_3451_);
if (v___x_3452_ == 0)
{
lean_object* v___x_3454_; 
lean_dec_ref(v_es_3446_);
lean_dec_ref(v_f_3438_);
if (v_isShared_3449_ == 0)
{
lean_ctor_set_tag(v___x_3448_, 1);
lean_ctor_set(v___x_3448_, 0, v_x_3440_);
v___x_3454_ = v___x_3448_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_x_3440_);
v___x_3454_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
lean_object* v___x_3455_; 
v___x_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3454_);
return v___x_3455_;
}
}
else
{
uint8_t v___x_3457_; 
v___x_3457_ = lean_nat_dec_le(v___x_3451_, v___x_3451_);
if (v___x_3457_ == 0)
{
if (v___x_3452_ == 0)
{
lean_object* v___x_3459_; 
lean_dec_ref(v_es_3446_);
lean_dec_ref(v_f_3438_);
if (v_isShared_3449_ == 0)
{
lean_ctor_set_tag(v___x_3448_, 1);
lean_ctor_set(v___x_3448_, 0, v_x_3440_);
v___x_3459_ = v___x_3448_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_x_3440_);
v___x_3459_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
lean_object* v___x_3460_; 
v___x_3460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3459_);
return v___x_3460_;
}
}
else
{
size_t v___x_3462_; size_t v___x_3463_; lean_object* v___x_3464_; 
lean_del_object(v___x_3448_);
v___x_3462_ = ((size_t)0ULL);
v___x_3463_ = lean_usize_of_nat(v___x_3451_);
v___x_3464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3438_, v_es_3446_, v___x_3462_, v___x_3463_, v_x_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
lean_dec_ref(v_es_3446_);
return v___x_3464_;
}
}
else
{
size_t v___x_3465_; size_t v___x_3466_; lean_object* v___x_3467_; 
lean_del_object(v___x_3448_);
v___x_3465_ = ((size_t)0ULL);
v___x_3466_ = lean_usize_of_nat(v___x_3451_);
v___x_3467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3438_, v_es_3446_, v___x_3465_, v___x_3466_, v_x_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
lean_dec_ref(v_es_3446_);
return v___x_3467_;
}
}
}
}
else
{
lean_object* v_ks_3469_; lean_object* v_vs_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
v_ks_3469_ = lean_ctor_get(v_x_3439_, 0);
lean_inc_ref(v_ks_3469_);
v_vs_3470_ = lean_ctor_get(v_x_3439_, 1);
lean_inc_ref(v_vs_3470_);
lean_dec_ref_known(v_x_3439_, 2);
v___x_3471_ = lean_unsigned_to_nat(0u);
v___x_3472_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3438_, v_ks_3469_, v_vs_3470_, v___x_3471_, v_x_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
lean_dec_ref(v_vs_3470_);
lean_dec_ref(v_ks_3469_);
return v___x_3472_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_f_3473_, lean_object* v_as_3474_, size_t v_i_3475_, size_t v_stop_3476_, lean_object* v_b_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_){
_start:
{
lean_object* v_a_3484_; lean_object* v___y_3489_; uint8_t v___x_3492_; 
v___x_3492_ = lean_usize_dec_eq(v_i_3475_, v_stop_3476_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3493_; 
v___x_3493_ = lean_array_uget_borrowed(v_as_3474_, v_i_3475_);
switch(lean_obj_tag(v___x_3493_))
{
case 0:
{
lean_object* v_key_3494_; lean_object* v_val_3495_; lean_object* v___x_3496_; 
v_key_3494_ = lean_ctor_get(v___x_3493_, 0);
v_val_3495_ = lean_ctor_get(v___x_3493_, 1);
lean_inc_ref(v_f_3473_);
lean_inc(v___y_3481_);
lean_inc_ref(v___y_3480_);
lean_inc(v___y_3479_);
lean_inc_ref(v___y_3478_);
lean_inc(v_val_3495_);
lean_inc(v_key_3494_);
v___x_3496_ = lean_apply_8(v_f_3473_, v_b_3477_, v_key_3494_, v_val_3495_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, lean_box(0));
v___y_3489_ = v___x_3496_;
goto v___jp_3488_;
}
case 1:
{
lean_object* v_node_3497_; lean_object* v___x_3498_; 
v_node_3497_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_node_3497_);
lean_inc_ref(v_f_3473_);
v___x_3498_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3473_, v_node_3497_, v_b_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
v___y_3489_ = v___x_3498_;
goto v___jp_3488_;
}
default: 
{
v_a_3484_ = v_b_3477_;
goto v___jp_3483_;
}
}
}
else
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
lean_dec_ref(v_f_3473_);
v___x_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3499_, 0, v_b_3477_);
v___x_3500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
return v___x_3500_;
}
v___jp_3483_:
{
size_t v___x_3485_; size_t v___x_3486_; 
v___x_3485_ = ((size_t)1ULL);
v___x_3486_ = lean_usize_add(v_i_3475_, v___x_3485_);
v_i_3475_ = v___x_3486_;
v_b_3477_ = v_a_3484_;
goto _start;
}
v___jp_3488_:
{
if (lean_obj_tag(v___y_3489_) == 0)
{
lean_object* v_a_3490_; 
v_a_3490_ = lean_ctor_get(v___y_3489_, 0);
if (lean_obj_tag(v_a_3490_) == 0)
{
lean_dec_ref(v_f_3473_);
return v___y_3489_;
}
else
{
lean_object* v_a_3491_; 
lean_inc_ref(v_a_3490_);
lean_dec_ref_known(v___y_3489_, 1);
v_a_3491_ = lean_ctor_get(v_a_3490_, 0);
lean_inc(v_a_3491_);
lean_dec_ref_known(v_a_3490_, 1);
v_a_3484_ = v_a_3491_;
goto v___jp_3483_;
}
}
else
{
lean_dec_ref(v_f_3473_);
return v___y_3489_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_3501_, lean_object* v_as_3502_, lean_object* v_i_3503_, lean_object* v_stop_3504_, lean_object* v_b_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
size_t v_i_boxed_3511_; size_t v_stop_boxed_3512_; lean_object* v_res_3513_; 
v_i_boxed_3511_ = lean_unbox_usize(v_i_3503_);
lean_dec(v_i_3503_);
v_stop_boxed_3512_ = lean_unbox_usize(v_stop_3504_);
lean_dec(v_stop_3504_);
v_res_3513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3501_, v_as_3502_, v_i_boxed_3511_, v_stop_boxed_3512_, v_b_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec_ref(v_as_3502_);
return v_res_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_f_3514_, lean_object* v_x_3515_, lean_object* v_x_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3514_, v_x_3515_, v_x_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object* v_f_3523_, lean_object* v_s_3524_, lean_object* v_a_3525_, lean_object* v_b_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3532_, 0, v_a_3525_);
lean_ctor_set(v___x_3532_, 1, v_b_3526_);
lean_inc(v___y_3530_);
lean_inc_ref(v___y_3529_);
lean_inc(v___y_3528_);
lean_inc_ref(v___y_3527_);
v___x_3533_ = lean_apply_7(v_f_3523_, v___x_3532_, v_s_3524_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, lean_box(0));
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3560_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3536_ = v___x_3533_;
v_isShared_3537_ = v_isSharedCheck_3560_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3533_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3560_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
if (lean_obj_tag(v_a_3534_) == 0)
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3548_; 
v_a_3538_ = lean_ctor_get(v_a_3534_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v_a_3534_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3540_ = v_a_3534_;
v_isShared_3541_ = v_isSharedCheck_3548_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v_a_3534_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3548_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3538_);
v___x_3543_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
lean_object* v___x_3545_; 
if (v_isShared_3537_ == 0)
{
lean_ctor_set(v___x_3536_, 0, v___x_3543_);
v___x_3545_ = v___x_3536_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3543_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
else
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3559_; 
v_a_3549_ = lean_ctor_get(v_a_3534_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v_a_3534_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3551_ = v_a_3534_;
v_isShared_3552_ = v_isSharedCheck_3559_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v_a_3534_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3559_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3554_; 
if (v_isShared_3552_ == 0)
{
v___x_3554_ = v___x_3551_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_a_3549_);
v___x_3554_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
lean_object* v___x_3556_; 
if (v_isShared_3537_ == 0)
{
lean_ctor_set(v___x_3536_, 0, v___x_3554_);
v___x_3556_ = v___x_3536_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
v_a_3561_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3533_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3533_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object* v_f_3569_, lean_object* v_s_3570_, lean_object* v_a_3571_, lean_object* v_b_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_){
_start:
{
lean_object* v_res_3578_; 
v_res_3578_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(v_f_3569_, v_s_3570_, v_a_3571_, v_b_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object* v_map_3579_, lean_object* v_init_3580_, lean_object* v_f_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v___f_3587_; lean_object* v___x_3588_; 
v___f_3587_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3587_, 0, v_f_3581_);
lean_inc_ref(v_map_3579_);
v___x_3588_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v___f_3587_, v_map_3579_, v_init_3580_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3597_; 
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3591_ = v___x_3588_;
v_isShared_3592_ = v_isSharedCheck_3597_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3588_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3597_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v_a_3593_; lean_object* v___x_3595_; 
v_a_3593_ = lean_ctor_get(v_a_3589_, 0);
lean_inc(v_a_3593_);
lean_dec(v_a_3589_);
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 0, v_a_3593_);
v___x_3595_ = v___x_3591_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3593_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
else
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3605_; 
v_a_3598_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3600_ = v___x_3588_;
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3588_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3603_; 
if (v_isShared_3601_ == 0)
{
v___x_3603_ = v___x_3600_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_a_3598_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object* v_map_3606_, lean_object* v_init_3607_, lean_object* v_f_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_3606_, v_init_3607_, v_f_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec_ref(v_map_3606_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object* v___y_3615_){
_start:
{
lean_object* v___x_3617_; lean_object* v_env_3618_; lean_object* v___x_3619_; lean_object* v_ext_3620_; lean_object* v_toEnvExtension_3621_; lean_object* v_asyncMode_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v_categories_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3617_ = lean_st_ref_get(v___y_3615_);
v_env_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc_ref_n(v_env_3618_, 2);
lean_dec(v___x_3617_);
v___x_3619_ = l_Lean_Parser_parserExtension;
v_ext_3620_ = lean_ctor_get(v___x_3619_, 1);
v_toEnvExtension_3621_ = lean_ctor_get(v_ext_3620_, 0);
v_asyncMode_3622_ = lean_ctor_get(v_toEnvExtension_3621_, 2);
v___x_3623_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3624_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3623_, v___x_3619_, v_env_3618_, v_asyncMode_3622_);
v_categories_3625_ = lean_ctor_get(v___x_3624_, 2);
lean_inc_ref(v_categories_3625_);
lean_dec(v___x_3624_);
v___x_3626_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3627_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3625_, v___x_3626_);
lean_dec_ref(v_categories_3625_);
if (lean_obj_tag(v___x_3627_) == 1)
{
lean_object* v_val_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3665_; 
v_val_3628_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3630_ = v___x_3627_;
v_isShared_3631_ = v_isSharedCheck_3665_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_val_3628_);
lean_dec(v___x_3627_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3665_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___y_3633_; lean_object* v___x_3642_; lean_object* v_toEnvExtension_3643_; lean_object* v_exportEntriesFn_3644_; lean_object* v_asyncMode_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v_importedEntries_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v_exported_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; uint8_t v___x_3657_; 
v___x_3642_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3643_ = lean_ctor_get(v___x_3642_, 0);
v_exportEntriesFn_3644_ = lean_ctor_get(v___x_3642_, 4);
v_asyncMode_3645_ = lean_ctor_get(v_toEnvExtension_3643_, 2);
v___x_3646_ = lean_box(1);
v___x_3647_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3648_ = lean_box(0);
lean_inc_ref_n(v_env_3618_, 2);
v___x_3649_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3647_, v_toEnvExtension_3643_, v_env_3618_, v_asyncMode_3645_, v___x_3648_);
v_importedEntries_3650_ = lean_ctor_get(v___x_3649_, 0);
lean_inc_ref(v_importedEntries_3650_);
lean_dec(v___x_3649_);
v___x_3651_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3646_, v___x_3642_, v_env_3618_, v_asyncMode_3645_, v___x_3648_);
lean_inc_ref(v_exportEntriesFn_3644_);
v___x_3652_ = lean_apply_2(v_exportEntriesFn_3644_, v_env_3618_, v___x_3651_);
v_exported_3653_ = lean_ctor_get(v___x_3652_, 0);
lean_inc(v_exported_3653_);
lean_dec_ref(v___x_3652_);
v___x_3654_ = lean_array_push(v_importedEntries_3650_, v_exported_3653_);
v___x_3655_ = lean_unsigned_to_nat(0u);
v___x_3656_ = lean_array_get_size(v___x_3654_);
v___x_3657_ = lean_nat_dec_lt(v___x_3655_, v___x_3656_);
if (v___x_3657_ == 0)
{
lean_dec_ref(v___x_3654_);
v___y_3633_ = v___x_3646_;
goto v___jp_3632_;
}
else
{
uint8_t v___x_3658_; 
v___x_3658_ = lean_nat_dec_le(v___x_3656_, v___x_3656_);
if (v___x_3658_ == 0)
{
if (v___x_3657_ == 0)
{
lean_dec_ref(v___x_3654_);
v___y_3633_ = v___x_3646_;
goto v___jp_3632_;
}
else
{
size_t v___x_3659_; size_t v___x_3660_; lean_object* v___x_3661_; 
v___x_3659_ = ((size_t)0ULL);
v___x_3660_ = lean_usize_of_nat(v___x_3656_);
v___x_3661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3654_, v___x_3659_, v___x_3660_, v___x_3646_);
lean_dec_ref(v___x_3654_);
v___y_3633_ = v___x_3661_;
goto v___jp_3632_;
}
}
else
{
size_t v___x_3662_; size_t v___x_3663_; lean_object* v___x_3664_; 
v___x_3662_ = ((size_t)0ULL);
v___x_3663_ = lean_usize_of_nat(v___x_3656_);
v___x_3664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3654_, v___x_3662_, v___x_3663_, v___x_3646_);
lean_dec_ref(v___x_3654_);
v___y_3633_ = v___x_3664_;
goto v___jp_3632_;
}
}
v___jp_3632_:
{
lean_object* v_tables_3634_; lean_object* v_leadingTable_3635_; lean_object* v_trailingTable_3636_; lean_object* v_firstTokens_3637_; lean_object* v_firstTokens_3638_; lean_object* v___x_3640_; 
v_tables_3634_ = lean_ctor_get(v_val_3628_, 2);
v_leadingTable_3635_ = lean_ctor_get(v_tables_3634_, 0);
v_trailingTable_3636_ = lean_ctor_get(v_tables_3634_, 2);
lean_inc(v_trailingTable_3636_);
lean_inc(v_leadingTable_3635_);
lean_inc(v_val_3628_);
v_firstTokens_3637_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3628_, v_leadingTable_3635_, v___y_3633_);
v_firstTokens_3638_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3628_, v_trailingTable_3636_, v_firstTokens_3637_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set_tag(v___x_3630_, 0);
lean_ctor_set(v___x_3630_, 0, v_firstTokens_3638_);
v___x_3640_ = v___x_3630_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_firstTokens_3638_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
}
else
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
lean_dec(v___x_3627_);
lean_dec_ref(v_env_3618_);
v___x_3666_ = lean_box(1);
v___x_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3666_);
return v___x_3667_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
lean_object* v_res_3670_; 
v_res_3670_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_3668_);
lean_dec(v___y_3668_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t v_includeUnnamed_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_){
_start:
{
lean_object* v___x_3679_; lean_object* v_env_3680_; lean_object* v___x_3681_; lean_object* v_toEnvExtension_3682_; lean_object* v_exportEntriesFn_3683_; lean_object* v_asyncMode_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v_importedEntries_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v_exported_3692_; lean_object* v___x_3693_; size_t v_sz_3694_; size_t v___x_3695_; lean_object* v___x_3696_; 
v___x_3679_ = lean_st_ref_get(v_a_3677_);
v_env_3680_ = lean_ctor_get(v___x_3679_, 0);
lean_inc_ref_n(v_env_3680_, 4);
lean_dec(v___x_3679_);
v___x_3681_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_3682_ = lean_ctor_get(v___x_3681_, 0);
v_exportEntriesFn_3683_ = lean_ctor_get(v___x_3681_, 4);
v_asyncMode_3684_ = lean_ctor_get(v_toEnvExtension_3682_, 2);
v___x_3685_ = lean_box(1);
v___x_3686_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_3687_ = lean_box(0);
v___x_3688_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3686_, v_toEnvExtension_3682_, v_env_3680_, v_asyncMode_3684_, v___x_3687_);
v_importedEntries_3689_ = lean_ctor_get(v___x_3688_, 0);
lean_inc_ref(v_importedEntries_3689_);
lean_dec(v___x_3688_);
v___x_3690_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3685_, v___x_3681_, v_env_3680_, v_asyncMode_3684_, v___x_3687_);
lean_inc_ref(v_exportEntriesFn_3683_);
v___x_3691_ = lean_apply_2(v_exportEntriesFn_3683_, v_env_3680_, v___x_3690_);
v_exported_3692_ = lean_ctor_get(v___x_3691_, 0);
lean_inc(v_exported_3692_);
lean_dec_ref(v___x_3691_);
v___x_3693_ = lean_array_push(v_importedEntries_3689_, v_exported_3692_);
v_sz_3694_ = lean_array_size(v___x_3693_);
v___x_3695_ = ((size_t)0ULL);
v___x_3696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v___x_3693_, v_sz_3694_, v___x_3695_, v___x_3685_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
lean_dec_ref(v___x_3693_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_object* v_a_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3721_; 
v_a_3697_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3699_ = v___x_3696_;
v_isShared_3700_ = v_isSharedCheck_3721_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_a_3697_);
lean_dec(v___x_3696_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3721_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___x_3701_; lean_object* v_ext_3702_; lean_object* v_toEnvExtension_3703_; lean_object* v_asyncMode_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v_categories_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3701_ = l_Lean_Parser_parserExtension;
v_ext_3702_ = lean_ctor_get(v___x_3701_, 1);
v_toEnvExtension_3703_ = lean_ctor_get(v_ext_3702_, 0);
v_asyncMode_3704_ = lean_ctor_get(v_toEnvExtension_3703_, 2);
v___x_3705_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref(v_env_3680_);
v___x_3706_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3705_, v___x_3701_, v_env_3680_, v_asyncMode_3704_);
v_categories_3707_ = lean_ctor_get(v___x_3706_, 2);
lean_inc_ref(v_categories_3707_);
lean_dec(v___x_3706_);
v___x_3708_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0));
v___x_3709_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3710_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3707_, v___x_3709_);
lean_dec_ref(v_categories_3707_);
if (lean_obj_tag(v___x_3710_) == 1)
{
lean_object* v_val_3711_; lean_object* v___x_3712_; lean_object* v_a_3713_; lean_object* v_kinds_3714_; lean_object* v___x_3715_; lean_object* v___f_3716_; lean_object* v___x_3717_; 
lean_del_object(v___x_3699_);
v_val_3711_ = lean_ctor_get(v___x_3710_, 0);
lean_inc(v_val_3711_);
lean_dec_ref_known(v___x_3710_, 1);
v___x_3712_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v_a_3677_);
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
lean_inc(v_a_3713_);
lean_dec_ref(v___x_3712_);
v_kinds_3714_ = lean_ctor_get(v_val_3711_, 1);
lean_inc_ref(v_kinds_3714_);
lean_dec(v_val_3711_);
v___x_3715_ = lean_box(v_includeUnnamed_3673_);
v___f_3716_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed), 12, 5);
lean_closure_set(v___f_3716_, 0, v_env_3680_);
lean_closure_set(v___f_3716_, 1, v___x_3687_);
lean_closure_set(v___f_3716_, 2, v_a_3697_);
lean_closure_set(v___f_3716_, 3, v_a_3713_);
lean_closure_set(v___f_3716_, 4, v___x_3715_);
v___x_3717_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_kinds_3714_, v___x_3708_, v___f_3716_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
lean_dec_ref(v_kinds_3714_);
return v___x_3717_;
}
else
{
lean_object* v___x_3719_; 
lean_dec(v___x_3710_);
lean_dec(v_a_3697_);
lean_dec_ref(v_env_3680_);
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 0, v___x_3708_);
v___x_3719_ = v___x_3699_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v___x_3708_);
v___x_3719_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
return v___x_3719_;
}
}
}
}
else
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
lean_dec_ref(v_env_3680_);
v_a_3722_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3724_ = v___x_3696_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3696_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3725_ == 0)
{
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3722_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object* v_includeUnnamed_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_){
_start:
{
uint8_t v_includeUnnamed_boxed_3736_; lean_object* v_res_3737_; 
v_includeUnnamed_boxed_3736_ = lean_unbox(v_includeUnnamed_3730_);
v_res_3737_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v_includeUnnamed_boxed_3736_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_);
lean_dec(v_a_3734_);
lean_dec_ref(v_a_3733_);
lean_dec(v_a_3732_);
lean_dec_ref(v_a_3731_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object* v_as_3738_, size_t v_sz_3739_, size_t v_i_3740_, lean_object* v_b_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
lean_object* v___x_3747_; 
v___x_3747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_3738_, v_sz_3739_, v_i_3740_, v_b_3741_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object* v_as_3748_, lean_object* v_sz_3749_, lean_object* v_i_3750_, lean_object* v_b_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
size_t v_sz_boxed_3757_; size_t v_i_boxed_3758_; lean_object* v_res_3759_; 
v_sz_boxed_3757_ = lean_unbox_usize(v_sz_3749_);
lean_dec(v_sz_3749_);
v_i_boxed_3758_ = lean_unbox_usize(v_i_3750_);
lean_dec(v_i_3750_);
v_res_3759_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(v_as_3748_, v_sz_boxed_3757_, v_i_boxed_3758_, v_b_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec_ref(v_as_3748_);
return v_res_3759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
lean_object* v___x_3765_; 
v___x_3765_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_3763_);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object* v_00_u03c3_3772_, lean_object* v_00_u03b2_3773_, lean_object* v_map_3774_, lean_object* v_init_3775_, lean_object* v_f_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
lean_object* v___x_3782_; 
v___x_3782_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_3774_, v_init_3775_, v_f_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object* v_00_u03c3_3783_, lean_object* v_00_u03b2_3784_, lean_object* v_map_3785_, lean_object* v_init_3786_, lean_object* v_f_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v_res_3793_; 
v_res_3793_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(v_00_u03c3_3783_, v_00_u03b2_3784_, v_map_3785_, v_init_3786_, v_f_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec_ref(v_map_3785_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object* v_map_3794_, lean_object* v_f_3795_, lean_object* v_init_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v___x_3802_; 
v___x_3802_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3795_, v_map_3794_, v_init_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object* v_map_3803_, lean_object* v_f_3804_, lean_object* v_init_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v_res_3811_; 
v_res_3811_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(v_map_3803_, v_f_3804_, v_init_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object* v_00_u03c3_3812_, lean_object* v_00_u03c3_3813_, lean_object* v_00_u03b2_3814_, lean_object* v_map_3815_, lean_object* v_f_3816_, lean_object* v_init_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v___x_3823_; 
v___x_3823_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3816_, v_map_3815_, v_init_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
return v___x_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object* v_00_u03c3_3824_, lean_object* v_00_u03c3_3825_, lean_object* v_00_u03b2_3826_, lean_object* v_map_3827_, lean_object* v_f_3828_, lean_object* v_init_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(v_00_u03c3_3824_, v_00_u03c3_3825_, v_00_u03b2_3826_, v_map_3827_, v_f_3828_, v_init_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object* v_00_u03c3_3836_, lean_object* v_00_u03c3_3837_, lean_object* v_00_u03b1_3838_, lean_object* v_00_u03b2_3839_, lean_object* v_f_3840_, lean_object* v_x_3841_, lean_object* v_x_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
lean_object* v___x_3848_; 
v___x_3848_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3840_, v_x_3841_, v_x_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03c3_3849_, lean_object* v_00_u03c3_3850_, lean_object* v_00_u03b1_3851_, lean_object* v_00_u03b2_3852_, lean_object* v_f_3853_, lean_object* v_x_3854_, lean_object* v_x_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_){
_start:
{
lean_object* v_res_3861_; 
v_res_3861_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(v_00_u03c3_3849_, v_00_u03c3_3850_, v_00_u03b1_3851_, v_00_u03b2_3852_, v_f_3853_, v_x_3854_, v_x_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
return v_res_3861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_3862_, lean_object* v_00_u03b2_3863_, lean_object* v_00_u03c3_3864_, lean_object* v_00_u03c3_3865_, lean_object* v_f_3866_, lean_object* v_as_3867_, size_t v_i_3868_, size_t v_stop_3869_, lean_object* v_b_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
lean_object* v___x_3876_; 
v___x_3876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3866_, v_as_3867_, v_i_3868_, v_stop_3869_, v_b_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_3877_, lean_object* v_00_u03b2_3878_, lean_object* v_00_u03c3_3879_, lean_object* v_00_u03c3_3880_, lean_object* v_f_3881_, lean_object* v_as_3882_, lean_object* v_i_3883_, lean_object* v_stop_3884_, lean_object* v_b_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_){
_start:
{
size_t v_i_boxed_3891_; size_t v_stop_boxed_3892_; lean_object* v_res_3893_; 
v_i_boxed_3891_ = lean_unbox_usize(v_i_3883_);
lean_dec(v_i_3883_);
v_stop_boxed_3892_ = lean_unbox_usize(v_stop_3884_);
lean_dec(v_stop_3884_);
v_res_3893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_3877_, v_00_u03b2_3878_, v_00_u03c3_3879_, v_00_u03c3_3880_, v_f_3881_, v_as_3882_, v_i_boxed_3891_, v_stop_boxed_3892_, v_b_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_);
lean_dec(v___y_3889_);
lean_dec_ref(v___y_3888_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec_ref(v_as_3882_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object* v_00_u03c3_3894_, lean_object* v_00_u03c3_3895_, lean_object* v_00_u03b1_3896_, lean_object* v_00_u03b2_3897_, lean_object* v_f_3898_, lean_object* v_keys_3899_, lean_object* v_vals_3900_, lean_object* v_heq_3901_, lean_object* v_i_3902_, lean_object* v_acc_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_){
_start:
{
lean_object* v___x_3909_; 
v___x_3909_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3898_, v_keys_3899_, v_vals_3900_, v_i_3902_, v_acc_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03c3_3910_, lean_object* v_00_u03c3_3911_, lean_object* v_00_u03b1_3912_, lean_object* v_00_u03b2_3913_, lean_object* v_f_3914_, lean_object* v_keys_3915_, lean_object* v_vals_3916_, lean_object* v_heq_3917_, lean_object* v_i_3918_, lean_object* v_acc_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(v_00_u03c3_3910_, v_00_u03c3_3911_, v_00_u03b1_3912_, v_00_u03b2_3913_, v_f_3914_, v_keys_3915_, v_vals_3916_, v_heq_3917_, v_i_3918_, v_acc_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
lean_dec(v___y_3923_);
lean_dec_ref(v___y_3922_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
lean_dec_ref(v_vals_3916_);
lean_dec_ref(v_keys_3915_);
return v_res_3925_;
}
}
lean_object* runtime_initialize_Lean_DocString(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Doc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Doc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_DocString(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Doc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Doc(builtin);
}
#ifdef __cplusplus
}
#endif
