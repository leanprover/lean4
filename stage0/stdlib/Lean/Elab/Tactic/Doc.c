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
lean_object* lean_st_ref_take(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
lean_object* l_Lean_TSyntax_getDocString(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Parser_Tactic_Doc_isTactic(lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_Doc_alternativeOfTactic(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "` is not a tactic"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "` is an alternative form of `"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7));
v___x_228_ = l_Lean_stringToMessageData(v___x_227_);
return v___x_228_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9));
v___x_231_ = l_Lean_stringToMessageData(v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11));
v___x_234_ = l_Lean_stringToMessageData(v___x_233_);
return v___x_234_;
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
lean_object* v_docs_262_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_301_; uint8_t v___y_302_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_318_; 
v_docs_262_ = l_Lean_Syntax_getArg(v___x_256_, v___x_255_);
lean_dec(v___x_256_);
if (v___x_257_ == 0)
{
lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_351_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16));
lean_inc(v_docs_262_);
v___x_352_ = l_Lean_Syntax_isOfKind(v_docs_262_, v___x_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; 
lean_dec(v_docs_262_);
lean_dec(v_x_247_);
v___x_353_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_354_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_353_, v_a_248_, v_a_249_);
return v___x_354_;
}
else
{
goto v___jp_344_;
}
}
else
{
goto v___jp_344_;
}
v___jp_263_:
{
lean_object* v___x_266_; lean_object* v_env_267_; lean_object* v_messages_268_; lean_object* v_scopes_269_; lean_object* v_usedQuotCtxts_270_; lean_object* v_nextMacroScope_271_; lean_object* v_maxRecDepth_272_; lean_object* v_ngen_273_; lean_object* v_auxDeclNGen_274_; lean_object* v_infoState_275_; lean_object* v_traceState_276_; lean_object* v_snapshotTasks_277_; lean_object* v_prevLinterStates_278_; lean_object* v_codeQualityEntryTasks_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_296_; 
v___x_266_ = lean_st_ref_take(v___y_265_);
v_env_267_ = lean_ctor_get(v___x_266_, 0);
v_messages_268_ = lean_ctor_get(v___x_266_, 1);
v_scopes_269_ = lean_ctor_get(v___x_266_, 2);
v_usedQuotCtxts_270_ = lean_ctor_get(v___x_266_, 3);
v_nextMacroScope_271_ = lean_ctor_get(v___x_266_, 4);
v_maxRecDepth_272_ = lean_ctor_get(v___x_266_, 5);
v_ngen_273_ = lean_ctor_get(v___x_266_, 6);
v_auxDeclNGen_274_ = lean_ctor_get(v___x_266_, 7);
v_infoState_275_ = lean_ctor_get(v___x_266_, 8);
v_traceState_276_ = lean_ctor_get(v___x_266_, 9);
v_snapshotTasks_277_ = lean_ctor_get(v___x_266_, 10);
v_prevLinterStates_278_ = lean_ctor_get(v___x_266_, 11);
v_codeQualityEntryTasks_279_ = lean_ctor_get(v___x_266_, 12);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_296_ == 0)
{
v___x_281_ = v___x_266_;
v_isShared_282_ = v_isSharedCheck_296_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_codeQualityEntryTasks_279_);
lean_inc(v_prevLinterStates_278_);
lean_inc(v_snapshotTasks_277_);
lean_inc(v_traceState_276_);
lean_inc(v_infoState_275_);
lean_inc(v_auxDeclNGen_274_);
lean_inc(v_ngen_273_);
lean_inc(v_maxRecDepth_272_);
lean_inc(v_nextMacroScope_271_);
lean_inc(v_usedQuotCtxts_270_);
lean_inc(v_scopes_269_);
lean_inc(v_messages_268_);
lean_inc(v_env_267_);
lean_dec(v___x_266_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_296_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v_toEnvExtension_284_; lean_object* v_asyncMode_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_283_ = l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
v_toEnvExtension_284_ = lean_ctor_get(v___x_283_, 0);
v_asyncMode_285_ = lean_ctor_get(v_toEnvExtension_284_, 2);
v___x_286_ = l_Lean_TSyntax_getDocString(v_docs_262_);
lean_dec(v_docs_262_);
v___x_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_287_, 0, v___y_264_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = lean_box(0);
v___x_289_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_283_, v_env_267_, v___x_287_, v_asyncMode_285_, v___x_288_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_289_);
v___x_291_ = v___x_281_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_messages_268_);
lean_ctor_set(v_reuseFailAlloc_295_, 2, v_scopes_269_);
lean_ctor_set(v_reuseFailAlloc_295_, 3, v_usedQuotCtxts_270_);
lean_ctor_set(v_reuseFailAlloc_295_, 4, v_nextMacroScope_271_);
lean_ctor_set(v_reuseFailAlloc_295_, 5, v_maxRecDepth_272_);
lean_ctor_set(v_reuseFailAlloc_295_, 6, v_ngen_273_);
lean_ctor_set(v_reuseFailAlloc_295_, 7, v_auxDeclNGen_274_);
lean_ctor_set(v_reuseFailAlloc_295_, 8, v_infoState_275_);
lean_ctor_set(v_reuseFailAlloc_295_, 9, v_traceState_276_);
lean_ctor_set(v_reuseFailAlloc_295_, 10, v_snapshotTasks_277_);
lean_ctor_set(v_reuseFailAlloc_295_, 11, v_prevLinterStates_278_);
lean_ctor_set(v_reuseFailAlloc_295_, 12, v_codeQualityEntryTasks_279_);
v___x_291_ = v_reuseFailAlloc_295_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = lean_st_ref_put(v___y_265_, v___x_291_);
v___x_293_ = lean_box(0);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
}
}
v___jp_297_:
{
if (v___y_302_ == 0)
{
lean_dec(v___y_301_);
v___y_264_ = v___y_299_;
v___y_265_ = v___y_298_;
goto v___jp_263_;
}
else
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
lean_dec(v_docs_262_);
v___x_303_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8);
v___x_304_ = l_Lean_MessageData_ofConstName(v___y_299_, v___x_257_);
v___x_305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10);
v___x_307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_305_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v___y_301_, v___x_307_, v___y_300_, v___y_298_);
lean_dec(v___y_301_);
return v___x_308_;
}
}
v___jp_309_:
{
lean_object* v___x_314_; lean_object* v_env_315_; uint8_t v___x_316_; 
v___x_314_ = lean_st_ref_get(v___y_313_);
v_env_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc_ref(v_env_315_);
lean_dec(v___x_314_);
v___x_316_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_315_, v___y_310_);
if (v___x_316_ == 0)
{
v___y_298_ = v___y_313_;
v___y_299_ = v___y_310_;
v___y_300_ = v___y_312_;
v___y_301_ = v___y_311_;
v___y_302_ = v___x_259_;
goto v___jp_297_;
}
else
{
v___y_298_ = v___y_313_;
v___y_299_ = v___y_310_;
v___y_300_ = v___y_312_;
v___y_301_ = v___y_311_;
v___y_302_ = v___x_257_;
goto v___jp_297_;
}
}
v___jp_317_:
{
lean_object* v___x_319_; lean_object* v___f_320_; lean_object* v___x_321_; 
v___x_319_ = lean_box(0);
lean_inc(v___y_318_);
v___f_320_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed), 9, 2);
lean_closure_set(v___f_320_, 0, v___y_318_);
lean_closure_set(v___f_320_, 1, v___x_319_);
v___x_321_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_320_, v_a_248_, v_a_249_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v___x_323_; lean_object* v_env_324_; lean_object* v___x_325_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc_n(v_a_322_, 2);
lean_dec_ref_known(v___x_321_, 1);
v___x_323_ = lean_st_ref_get(v_a_249_);
v_env_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc_ref(v_env_324_);
lean_dec(v___x_323_);
v___x_325_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_324_, v_a_322_);
if (lean_obj_tag(v___x_325_) == 1)
{
lean_object* v_val_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
lean_dec(v_docs_262_);
v_val_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_val_326_);
lean_dec_ref_known(v___x_325_, 1);
v___x_327_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8);
v___x_328_ = l_Lean_MessageData_ofConstName(v_a_322_, v___x_257_);
v___x_329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_327_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_329_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = l_Lean_MessageData_ofConstName(v_val_326_, v___x_257_);
v___x_333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_331_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
v___x_334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v___x_327_);
v___x_335_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v___y_318_, v___x_334_, v_a_248_, v_a_249_);
lean_dec(v___y_318_);
return v___x_335_;
}
else
{
lean_dec(v___x_325_);
v___y_310_ = v_a_322_;
v___y_311_ = v___y_318_;
v___y_312_ = v_a_248_;
v___y_313_ = v_a_249_;
goto v___jp_309_;
}
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_dec(v___y_318_);
lean_dec(v_docs_262_);
v_a_336_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_321_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_321_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
v___jp_344_:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_unsigned_to_nat(2u);
v___x_346_ = l_Lean_Syntax_getArg(v_x_247_, v___x_345_);
lean_dec(v_x_247_);
if (v___x_257_ == 0)
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14));
lean_inc(v___x_346_);
v___x_348_ = l_Lean_Syntax_isOfKind(v___x_346_, v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec(v___x_346_);
lean_dec(v_docs_262_);
v___x_349_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_350_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_349_, v_a_248_, v_a_249_);
return v___x_350_;
}
else
{
v___y_318_ = v___x_346_;
goto v___jp_317_;
}
}
else
{
v___y_318_ = v___x_346_;
goto v___jp_317_;
}
}
}
}
else
{
lean_object* v___x_355_; lean_object* v_cmd_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
lean_dec(v___x_256_);
v___x_355_ = lean_unsigned_to_nat(1u);
v_cmd_356_ = l_Lean_Syntax_getArg(v_x_247_, v___x_355_);
lean_dec(v_x_247_);
v___x_357_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18);
v___x_358_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_cmd_356_, v___x_357_, v_a_248_, v_a_249_);
lean_dec(v_cmd_356_);
return v___x_358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed(lean_object* v_x_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension(v_x_359_, v_a_360_, v_a_361_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(lean_object* v_msgData_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msgData_364_, v___y_366_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___boxed(lean_object* v_msgData_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(v_msgData_369_, v___y_370_, v___y_371_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(lean_object* v_00_u03b1_374_, lean_object* v_msg_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v_msg_375_, v___y_376_, v___y_377_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___boxed(lean_object* v_00_u03b1_380_, lean_object* v_msg_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(v_00_u03b1_380_, v_msg_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(lean_object* v_00_u03b1_386_, lean_object* v_ref_387_, lean_object* v_msg_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_ref_387_, v_msg_388_, v___y_389_, v___y_390_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___boxed(lean_object* v_00_u03b1_393_, lean_object* v_ref_394_, lean_object* v_msg_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(v_00_u03b1_393_, v_ref_394_, v_msg_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v_ref_394_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(lean_object* v_msgData_400_, lean_object* v_macroStack_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(v_msgData_400_, v_macroStack_401_, v___y_403_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___boxed(lean_object* v_msgData_406_, lean_object* v_macroStack_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(v_msgData_406_, v_macroStack_407_, v___y_408_, v___y_409_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1(){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_423_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_424_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4));
v___x_425_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_426_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed), 4, 0);
v___x_427_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_423_, v___x_424_, v___x_425_, v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3(){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_456_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_457_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6));
v___x_458_ = l_Lean_addBuiltinDeclarationRanges(v___x_456_, v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object* v_a_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
return v_res_460_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0));
v___x_463_ = l_Lean_stringToMessageData(v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(lean_object* v_stx_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_val_476_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_unsigned_to_nat(1u);
v___x_484_ = l_Lean_Syntax_getArg(v_stx_465_, v___x_483_);
switch(lean_obj_tag(v___x_484_))
{
case 2:
{
lean_object* v_val_485_; 
lean_dec(v_stx_465_);
v_val_485_ = lean_ctor_get(v___x_484_, 1);
lean_inc_ref(v_val_485_);
lean_dec_ref_known(v___x_484_, 2);
v_val_476_ = v_val_485_;
goto v___jp_475_;
}
case 1:
{
lean_object* v_kind_486_; 
v_kind_486_ = lean_ctor_get(v___x_484_, 1);
lean_inc(v_kind_486_);
if (lean_obj_tag(v_kind_486_) == 1)
{
lean_object* v_pre_487_; 
v_pre_487_ = lean_ctor_get(v_kind_486_, 0);
lean_inc(v_pre_487_);
if (lean_obj_tag(v_pre_487_) == 1)
{
lean_object* v_pre_488_; 
v_pre_488_ = lean_ctor_get(v_pre_487_, 0);
lean_inc(v_pre_488_);
if (lean_obj_tag(v_pre_488_) == 1)
{
lean_object* v_pre_489_; 
v_pre_489_ = lean_ctor_get(v_pre_488_, 0);
lean_inc(v_pre_489_);
if (lean_obj_tag(v_pre_489_) == 1)
{
lean_object* v_pre_490_; 
v_pre_490_ = lean_ctor_get(v_pre_489_, 0);
if (lean_obj_tag(v_pre_490_) == 0)
{
lean_object* v_str_491_; lean_object* v_str_492_; lean_object* v_str_493_; lean_object* v_str_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v_str_491_ = lean_ctor_get(v_kind_486_, 1);
lean_inc_ref(v_str_491_);
lean_dec_ref_known(v_kind_486_, 2);
v_str_492_ = lean_ctor_get(v_pre_487_, 1);
lean_inc_ref(v_str_492_);
lean_dec_ref_known(v_pre_487_, 2);
v_str_493_ = lean_ctor_get(v_pre_488_, 1);
lean_inc_ref(v_str_493_);
lean_dec_ref_known(v_pre_488_, 2);
v_str_494_ = lean_ctor_get(v_pre_489_, 1);
lean_inc_ref(v_str_494_);
lean_dec_ref_known(v_pre_489_, 2);
v___x_495_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0));
v___x_496_ = lean_string_dec_eq(v_str_494_, v___x_495_);
lean_dec_ref(v_str_494_);
if (v___x_496_ == 0)
{
lean_dec_ref(v_str_493_);
lean_dec_ref(v_str_492_);
lean_dec_ref(v_str_491_);
lean_dec_ref_known(v___x_484_, 3);
goto v___jp_469_;
}
else
{
lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_497_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1));
v___x_498_ = lean_string_dec_eq(v_str_493_, v___x_497_);
lean_dec_ref(v_str_493_);
if (v___x_498_ == 0)
{
lean_dec_ref(v_str_492_);
lean_dec_ref(v_str_491_);
lean_dec_ref_known(v___x_484_, 3);
goto v___jp_469_;
}
else
{
lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2));
v___x_500_ = lean_string_dec_eq(v_str_492_, v___x_499_);
lean_dec_ref(v_str_492_);
if (v___x_500_ == 0)
{
lean_dec_ref(v_str_491_);
lean_dec_ref_known(v___x_484_, 3);
goto v___jp_469_;
}
else
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2));
v___x_502_ = lean_string_dec_eq(v_str_491_, v___x_501_);
lean_dec_ref(v_str_491_);
if (v___x_502_ == 0)
{
lean_dec_ref_known(v___x_484_, 3);
goto v___jp_469_;
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_unsigned_to_nat(0u);
v___x_504_ = l_Lean_Syntax_getArg(v___x_484_, v___x_503_);
lean_dec_ref_known(v___x_484_, 3);
if (lean_obj_tag(v___x_504_) == 2)
{
lean_object* v_val_505_; 
lean_dec(v_stx_465_);
v_val_505_ = lean_ctor_get(v___x_504_, 1);
lean_inc_ref(v_val_505_);
lean_dec_ref_known(v___x_504_, 2);
v_val_476_ = v_val_505_;
goto v___jp_475_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
lean_dec(v___x_504_);
v___x_506_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1);
lean_inc(v_stx_465_);
v___x_507_ = l_Lean_MessageData_ofSyntax(v_stx_465_);
v___x_508_ = l_Lean_indentD(v___x_507_);
v___x_509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_506_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v___x_510_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_stx_465_, v___x_509_, v___y_466_, v___y_467_);
lean_dec(v_stx_465_);
return v___x_510_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_489_, 2);
lean_dec_ref_known(v_pre_488_, 2);
lean_dec_ref_known(v_pre_487_, 2);
lean_dec_ref_known(v_kind_486_, 2);
lean_dec_ref_known(v___x_484_, 3);
goto v___jp_469_;
}
}
else
{
lean_dec_ref_known(v_pre_488_, 2);
lean_dec(v_pre_489_);
lean_dec_ref_known(v_pre_487_, 2);
lean_dec_ref_known(v_kind_486_, 2);
lean_dec_ref_known(v___x_484_, 3);
goto v___jp_469_;
}
}
else
{
lean_dec(v_pre_488_);
lean_dec_ref_known(v_pre_487_, 2);
lean_dec_ref_known(v_kind_486_, 2);
lean_dec_ref_known(v___x_484_, 3);
goto v___jp_469_;
}
}
else
{
lean_dec_ref_known(v_kind_486_, 2);
lean_dec(v_pre_487_);
lean_dec_ref_known(v___x_484_, 3);
goto v___jp_469_;
}
}
else
{
lean_dec_ref_known(v___x_484_, 3);
lean_dec(v_kind_486_);
goto v___jp_469_;
}
}
default: 
{
lean_dec(v___x_484_);
goto v___jp_469_;
}
}
v___jp_469_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_470_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1);
lean_inc(v_stx_465_);
v___x_471_ = l_Lean_MessageData_ofSyntax(v_stx_465_);
v___x_472_ = l_Lean_indentD(v___x_471_);
v___x_473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_470_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_stx_465_, v___x_473_, v___y_466_, v___y_467_);
lean_dec(v_stx_465_);
return v___x_474_;
}
v___jp_475_:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_477_ = lean_unsigned_to_nat(0u);
v___x_478_ = lean_string_utf8_byte_size(v_val_476_);
v___x_479_ = lean_unsigned_to_nat(2u);
v___x_480_ = lean_nat_sub(v___x_478_, v___x_479_);
v___x_481_ = lean_string_utf8_extract(v_val_476_, v___x_477_, v___x_480_);
lean_dec(v___x_480_);
lean_dec_ref(v_val_476_);
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___boxed(lean_object* v_stx_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(v_stx_511_, v___y_512_, v___y_513_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
return v_res_515_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0));
v___x_518_ = l_Lean_stringToMessageData(v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(lean_object* v_x_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v_a_536_; lean_object* v_doc_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
lean_inc(v_x_528_);
v___x_606_ = l_Lean_Syntax_isOfKind(v_x_528_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; 
lean_dec(v_x_528_);
v___x_607_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_608_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_607_, v_a_529_, v_a_530_);
return v___x_608_;
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_609_ = lean_unsigned_to_nat(0u);
v___x_610_ = l_Lean_Syntax_getArg(v_x_528_, v___x_609_);
v___x_611_ = l_Lean_Syntax_isNone(v___x_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_610_);
v___x_613_ = l_Lean_Syntax_matchesNull(v___x_610_, v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; lean_object* v___x_615_; 
lean_dec(v___x_610_);
lean_dec(v_x_528_);
v___x_614_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_615_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_614_, v_a_529_, v_a_530_);
return v___x_615_;
}
else
{
lean_object* v_doc_616_; 
v_doc_616_ = l_Lean_Syntax_getArg(v___x_610_, v___x_609_);
lean_dec(v___x_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16));
lean_inc(v_doc_616_);
v___x_620_ = l_Lean_Syntax_isOfKind(v_doc_616_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; 
lean_dec(v_doc_616_);
lean_dec(v_x_528_);
v___x_621_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_622_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_621_, v_a_529_, v_a_530_);
return v___x_622_;
}
else
{
goto v___jp_617_;
}
}
else
{
goto v___jp_617_;
}
v___jp_617_:
{
lean_object* v___x_618_; 
v___x_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_618_, 0, v_doc_616_);
v_doc_571_ = v___x_618_;
v___y_572_ = v_a_529_;
v___y_573_ = v_a_530_;
goto v___jp_570_;
}
}
}
else
{
lean_object* v___x_623_; 
lean_dec(v___x_610_);
v___x_623_ = lean_box(0);
v_doc_571_ = v___x_623_;
v___y_572_ = v_a_529_;
v___y_573_ = v_a_530_;
goto v___jp_570_;
}
}
v___jp_532_:
{
lean_object* v___x_537_; lean_object* v_env_538_; lean_object* v_messages_539_; lean_object* v_scopes_540_; lean_object* v_usedQuotCtxts_541_; lean_object* v_nextMacroScope_542_; lean_object* v_maxRecDepth_543_; lean_object* v_ngen_544_; lean_object* v_auxDeclNGen_545_; lean_object* v_infoState_546_; lean_object* v_traceState_547_; lean_object* v_snapshotTasks_548_; lean_object* v_prevLinterStates_549_; lean_object* v_codeQualityEntryTasks_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_569_; 
v___x_537_ = lean_st_ref_take(v___y_534_);
v_env_538_ = lean_ctor_get(v___x_537_, 0);
v_messages_539_ = lean_ctor_get(v___x_537_, 1);
v_scopes_540_ = lean_ctor_get(v___x_537_, 2);
v_usedQuotCtxts_541_ = lean_ctor_get(v___x_537_, 3);
v_nextMacroScope_542_ = lean_ctor_get(v___x_537_, 4);
v_maxRecDepth_543_ = lean_ctor_get(v___x_537_, 5);
v_ngen_544_ = lean_ctor_get(v___x_537_, 6);
v_auxDeclNGen_545_ = lean_ctor_get(v___x_537_, 7);
v_infoState_546_ = lean_ctor_get(v___x_537_, 8);
v_traceState_547_ = lean_ctor_get(v___x_537_, 9);
v_snapshotTasks_548_ = lean_ctor_get(v___x_537_, 10);
v_prevLinterStates_549_ = lean_ctor_get(v___x_537_, 11);
v_codeQualityEntryTasks_550_ = lean_ctor_get(v___x_537_, 12);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_569_ == 0)
{
v___x_552_ = v___x_537_;
v_isShared_553_ = v_isSharedCheck_569_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_codeQualityEntryTasks_550_);
lean_inc(v_prevLinterStates_549_);
lean_inc(v_snapshotTasks_548_);
lean_inc(v_traceState_547_);
lean_inc(v_infoState_546_);
lean_inc(v_auxDeclNGen_545_);
lean_inc(v_ngen_544_);
lean_inc(v_maxRecDepth_543_);
lean_inc(v_nextMacroScope_542_);
lean_inc(v_usedQuotCtxts_541_);
lean_inc(v_scopes_540_);
lean_inc(v_messages_539_);
lean_inc(v_env_538_);
lean_dec(v___x_537_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_569_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v_toEnvExtension_555_; lean_object* v_asyncMode_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_554_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_555_ = lean_ctor_get(v___x_554_, 0);
v_asyncMode_556_ = lean_ctor_get(v_toEnvExtension_555_, 2);
v___x_557_ = l_Lean_TSyntax_getId(v___y_535_);
lean_dec(v___y_535_);
v___x_558_ = l_Lean_TSyntax_getString(v___y_533_);
lean_dec(v___y_533_);
v___x_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
lean_ctor_set(v___x_559_, 1, v_a_536_);
v___x_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_557_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_561_ = lean_box(0);
v___x_562_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_554_, v_env_538_, v___x_560_, v_asyncMode_556_, v___x_561_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_562_);
v___x_564_ = v___x_552_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_messages_539_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v_scopes_540_);
lean_ctor_set(v_reuseFailAlloc_568_, 3, v_usedQuotCtxts_541_);
lean_ctor_set(v_reuseFailAlloc_568_, 4, v_nextMacroScope_542_);
lean_ctor_set(v_reuseFailAlloc_568_, 5, v_maxRecDepth_543_);
lean_ctor_set(v_reuseFailAlloc_568_, 6, v_ngen_544_);
lean_ctor_set(v_reuseFailAlloc_568_, 7, v_auxDeclNGen_545_);
lean_ctor_set(v_reuseFailAlloc_568_, 8, v_infoState_546_);
lean_ctor_set(v_reuseFailAlloc_568_, 9, v_traceState_547_);
lean_ctor_set(v_reuseFailAlloc_568_, 10, v_snapshotTasks_548_);
lean_ctor_set(v_reuseFailAlloc_568_, 11, v_prevLinterStates_549_);
lean_ctor_set(v_reuseFailAlloc_568_, 12, v_codeQualityEntryTasks_550_);
v___x_564_ = v_reuseFailAlloc_568_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_565_ = lean_st_ref_put(v___y_534_, v___x_564_);
v___x_566_ = lean_box(0);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
}
}
v___jp_570_:
{
lean_object* v___x_574_; lean_object* v_tag_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_574_ = lean_unsigned_to_nat(2u);
v_tag_575_ = l_Lean_Syntax_getArg(v_x_528_, v___x_574_);
v___x_576_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14));
lean_inc(v_tag_575_);
v___x_577_ = l_Lean_Syntax_isOfKind(v_tag_575_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v_tag_575_);
lean_dec(v_doc_571_);
lean_dec(v_x_528_);
v___x_578_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_579_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_578_, v___y_572_, v___y_573_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; lean_object* v_user_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_580_ = lean_unsigned_to_nat(3u);
v_user_581_ = l_Lean_Syntax_getArg(v_x_528_, v___x_580_);
lean_dec(v_x_528_);
v___x_582_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3));
lean_inc(v_user_581_);
v___x_583_ = l_Lean_Syntax_isOfKind(v_user_581_, v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec(v_user_581_);
lean_dec(v_tag_575_);
lean_dec(v_doc_571_);
v___x_584_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_585_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_584_, v___y_572_, v___y_573_);
return v___x_585_;
}
else
{
if (lean_obj_tag(v_doc_571_) == 0)
{
lean_object* v___x_586_; 
v___x_586_ = lean_box(0);
v___y_533_ = v_user_581_;
v___y_534_ = v___y_573_;
v___y_535_ = v_tag_575_;
v_a_536_ = v___x_586_;
goto v___jp_532_;
}
else
{
lean_object* v_val_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_604_; 
v_val_587_ = lean_ctor_get(v_doc_571_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v_doc_571_);
if (v_isSharedCheck_604_ == 0)
{
v___x_589_ = v_doc_571_;
v_isShared_590_ = v_isSharedCheck_604_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_val_587_);
lean_dec(v_doc_571_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_604_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(v_val_587_, v___y_572_, v___y_573_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_594_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
lean_dec_ref_known(v___x_591_, 1);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v_a_592_);
v___x_594_ = v___x_589_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_592_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
v___y_533_ = v_user_581_;
v___y_534_ = v___y_573_;
v___y_535_ = v_tag_575_;
v_a_536_ = v___x_594_;
goto v___jp_532_;
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_del_object(v___x_589_);
lean_dec(v_user_581_);
lean_dec(v_tag_575_);
v_a_596_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_591_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_591_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed(lean_object* v_x_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(v_x_624_, v_a_625_, v_a_626_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1(){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_637_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_638_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
v___x_639_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_640_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed), 4, 0);
v___x_641_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_637_, v___x_638_, v___x_639_, v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object* v_a_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3(){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_670_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_671_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6));
v___x_672_ = l_Lean_addBuiltinDeclarationRanges(v___x_670_, v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object* v_a_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(lean_object* v___x_675_, lean_object* v_x_676_){
_start:
{
if (lean_obj_tag(v_x_676_) == 0)
{
lean_object* v___x_677_; 
v___x_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_675_);
return v___x_677_;
}
else
{
lean_dec_ref(v___x_675_);
lean_inc_ref(v_x_676_);
return v_x_676_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_678_, lean_object* v_x_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_678_, v_x_679_);
lean_dec(v_x_679_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(lean_object* v___x_681_, lean_object* v_k_682_, lean_object* v_t_683_){
_start:
{
if (lean_obj_tag(v_t_683_) == 0)
{
lean_object* v_size_684_; lean_object* v_k_685_; lean_object* v_v_686_; lean_object* v_l_687_; lean_object* v_r_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_1014_; 
v_size_684_ = lean_ctor_get(v_t_683_, 0);
v_k_685_ = lean_ctor_get(v_t_683_, 1);
v_v_686_ = lean_ctor_get(v_t_683_, 2);
v_l_687_ = lean_ctor_get(v_t_683_, 3);
v_r_688_ = lean_ctor_get(v_t_683_, 4);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_t_683_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_690_ = v_t_683_;
v_isShared_691_ = v_isSharedCheck_1014_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_r_688_);
lean_inc(v_l_687_);
lean_inc(v_v_686_);
lean_inc(v_k_685_);
lean_inc(v_size_684_);
lean_dec(v_t_683_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_1014_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
uint8_t v___x_692_; 
v___x_692_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_682_, v_k_685_);
switch(v___x_692_)
{
case 0:
{
lean_object* v_impl_693_; lean_object* v___x_694_; 
lean_del_object(v___x_690_);
lean_dec(v_size_684_);
v_impl_693_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_681_, v_k_682_, v_l_687_);
v___x_694_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_685_, v_v_686_, v_impl_693_, v_r_688_);
return v___x_694_;
}
case 1:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
lean_dec(v_k_685_);
v___x_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_695_, 0, v_v_686_);
v___x_696_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_681_, v___x_695_);
lean_dec_ref_known(v___x_695_, 1);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_del_object(v___x_690_);
lean_dec(v_size_684_);
lean_dec(v_k_682_);
if (lean_obj_tag(v_l_687_) == 0)
{
if (lean_obj_tag(v_r_688_) == 0)
{
lean_object* v_size_697_; lean_object* v_k_698_; lean_object* v_v_699_; lean_object* v_l_700_; lean_object* v_r_701_; lean_object* v_size_702_; lean_object* v_k_703_; lean_object* v_v_704_; lean_object* v_l_705_; lean_object* v_r_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v_size_697_ = lean_ctor_get(v_l_687_, 0);
v_k_698_ = lean_ctor_get(v_l_687_, 1);
v_v_699_ = lean_ctor_get(v_l_687_, 2);
v_l_700_ = lean_ctor_get(v_l_687_, 3);
v_r_701_ = lean_ctor_get(v_l_687_, 4);
lean_inc(v_r_701_);
v_size_702_ = lean_ctor_get(v_r_688_, 0);
v_k_703_ = lean_ctor_get(v_r_688_, 1);
v_v_704_ = lean_ctor_get(v_r_688_, 2);
v_l_705_ = lean_ctor_get(v_r_688_, 3);
lean_inc(v_l_705_);
v_r_706_ = lean_ctor_get(v_r_688_, 4);
v___x_707_ = lean_unsigned_to_nat(1u);
v___x_708_ = lean_nat_dec_lt(v_size_697_, v_size_702_);
if (v___x_708_ == 0)
{
lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_844_; 
lean_inc(v_l_700_);
lean_inc(v_v_699_);
lean_inc(v_k_698_);
v_isSharedCheck_844_ = !lean_is_exclusive(v_l_687_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; lean_object* v_unused_846_; lean_object* v_unused_847_; lean_object* v_unused_848_; lean_object* v_unused_849_; 
v_unused_845_ = lean_ctor_get(v_l_687_, 4);
lean_dec(v_unused_845_);
v_unused_846_ = lean_ctor_get(v_l_687_, 3);
lean_dec(v_unused_846_);
v_unused_847_ = lean_ctor_get(v_l_687_, 2);
lean_dec(v_unused_847_);
v_unused_848_ = lean_ctor_get(v_l_687_, 1);
lean_dec(v_unused_848_);
v_unused_849_ = lean_ctor_get(v_l_687_, 0);
lean_dec(v_unused_849_);
v___x_710_ = v_l_687_;
v_isShared_711_ = v_isSharedCheck_844_;
goto v_resetjp_709_;
}
else
{
lean_dec(v_l_687_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_844_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v_tree_713_; 
v___x_712_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_698_, v_v_699_, v_l_700_, v_r_701_);
v_tree_713_ = lean_ctor_get(v___x_712_, 2);
lean_inc(v_tree_713_);
if (lean_obj_tag(v_tree_713_) == 0)
{
lean_object* v_k_714_; lean_object* v_v_715_; lean_object* v_size_716_; lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v_k_714_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_k_714_);
v_v_715_ = lean_ctor_get(v___x_712_, 1);
lean_inc(v_v_715_);
lean_dec_ref(v___x_712_);
v_size_716_ = lean_ctor_get(v_tree_713_, 0);
v___x_717_ = lean_unsigned_to_nat(3u);
v___x_718_ = lean_nat_mul(v___x_717_, v_size_716_);
v___x_719_ = lean_nat_dec_lt(v___x_718_, v_size_702_);
lean_dec(v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
lean_dec(v_l_705_);
v___x_720_ = lean_nat_add(v___x_707_, v_size_716_);
v___x_721_ = lean_nat_add(v___x_720_, v_size_702_);
lean_dec(v___x_720_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 4, v_r_688_);
lean_ctor_set(v___x_710_, 3, v_tree_713_);
lean_ctor_set(v___x_710_, 2, v_v_715_);
lean_ctor_set(v___x_710_, 1, v_k_714_);
lean_ctor_set(v___x_710_, 0, v___x_721_);
v___x_723_ = v___x_710_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_k_714_);
lean_ctor_set(v_reuseFailAlloc_724_, 2, v_v_715_);
lean_ctor_set(v_reuseFailAlloc_724_, 3, v_tree_713_);
lean_ctor_set(v_reuseFailAlloc_724_, 4, v_r_688_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
else
{
lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_779_; 
lean_inc(v_r_706_);
lean_inc(v_v_704_);
lean_inc(v_k_703_);
lean_inc(v_size_702_);
v_isSharedCheck_779_ = !lean_is_exclusive(v_r_688_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; lean_object* v_unused_781_; lean_object* v_unused_782_; lean_object* v_unused_783_; lean_object* v_unused_784_; 
v_unused_780_ = lean_ctor_get(v_r_688_, 4);
lean_dec(v_unused_780_);
v_unused_781_ = lean_ctor_get(v_r_688_, 3);
lean_dec(v_unused_781_);
v_unused_782_ = lean_ctor_get(v_r_688_, 2);
lean_dec(v_unused_782_);
v_unused_783_ = lean_ctor_get(v_r_688_, 1);
lean_dec(v_unused_783_);
v_unused_784_ = lean_ctor_get(v_r_688_, 0);
lean_dec(v_unused_784_);
v___x_726_ = v_r_688_;
v_isShared_727_ = v_isSharedCheck_779_;
goto v_resetjp_725_;
}
else
{
lean_dec(v_r_688_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_779_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v_size_728_; lean_object* v_k_729_; lean_object* v_v_730_; lean_object* v_l_731_; lean_object* v_r_732_; lean_object* v_size_733_; lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v_size_728_ = lean_ctor_get(v_l_705_, 0);
v_k_729_ = lean_ctor_get(v_l_705_, 1);
v_v_730_ = lean_ctor_get(v_l_705_, 2);
v_l_731_ = lean_ctor_get(v_l_705_, 3);
v_r_732_ = lean_ctor_get(v_l_705_, 4);
v_size_733_ = lean_ctor_get(v_r_706_, 0);
v___x_734_ = lean_unsigned_to_nat(2u);
v___x_735_ = lean_nat_mul(v___x_734_, v_size_733_);
v___x_736_ = lean_nat_dec_lt(v_size_728_, v___x_735_);
lean_dec(v___x_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_764_; 
lean_inc(v_r_732_);
lean_inc(v_l_731_);
lean_inc(v_v_730_);
lean_inc(v_k_729_);
v_isSharedCheck_764_ = !lean_is_exclusive(v_l_705_);
if (v_isSharedCheck_764_ == 0)
{
lean_object* v_unused_765_; lean_object* v_unused_766_; lean_object* v_unused_767_; lean_object* v_unused_768_; lean_object* v_unused_769_; 
v_unused_765_ = lean_ctor_get(v_l_705_, 4);
lean_dec(v_unused_765_);
v_unused_766_ = lean_ctor_get(v_l_705_, 3);
lean_dec(v_unused_766_);
v_unused_767_ = lean_ctor_get(v_l_705_, 2);
lean_dec(v_unused_767_);
v_unused_768_ = lean_ctor_get(v_l_705_, 1);
lean_dec(v_unused_768_);
v_unused_769_ = lean_ctor_get(v_l_705_, 0);
lean_dec(v_unused_769_);
v___x_738_ = v_l_705_;
v_isShared_739_ = v_isSharedCheck_764_;
goto v_resetjp_737_;
}
else
{
lean_dec(v_l_705_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_764_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_754_; 
v___x_740_ = lean_nat_add(v___x_707_, v_size_716_);
v___x_741_ = lean_nat_add(v___x_740_, v_size_702_);
lean_dec(v_size_702_);
if (lean_obj_tag(v_l_731_) == 0)
{
lean_object* v_size_762_; 
v_size_762_ = lean_ctor_get(v_l_731_, 0);
lean_inc(v_size_762_);
v___y_754_ = v_size_762_;
goto v___jp_753_;
}
else
{
lean_object* v___x_763_; 
v___x_763_ = lean_unsigned_to_nat(0u);
v___y_754_ = v___x_763_;
goto v___jp_753_;
}
v___jp_742_:
{
lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_746_ = lean_nat_add(v___y_743_, v___y_745_);
lean_dec(v___y_745_);
lean_dec(v___y_743_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 4, v_r_706_);
lean_ctor_set(v___x_738_, 3, v_r_732_);
lean_ctor_set(v___x_738_, 2, v_v_704_);
lean_ctor_set(v___x_738_, 1, v_k_703_);
lean_ctor_set(v___x_738_, 0, v___x_746_);
v___x_748_ = v___x_738_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_k_703_);
lean_ctor_set(v_reuseFailAlloc_752_, 2, v_v_704_);
lean_ctor_set(v_reuseFailAlloc_752_, 3, v_r_732_);
lean_ctor_set(v_reuseFailAlloc_752_, 4, v_r_706_);
v___x_748_ = v_reuseFailAlloc_752_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_750_; 
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 4, v___x_748_);
lean_ctor_set(v___x_726_, 3, v___y_744_);
lean_ctor_set(v___x_726_, 2, v_v_730_);
lean_ctor_set(v___x_726_, 1, v_k_729_);
lean_ctor_set(v___x_726_, 0, v___x_741_);
v___x_750_ = v___x_726_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_k_729_);
lean_ctor_set(v_reuseFailAlloc_751_, 2, v_v_730_);
lean_ctor_set(v_reuseFailAlloc_751_, 3, v___y_744_);
lean_ctor_set(v_reuseFailAlloc_751_, 4, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
v___jp_753_:
{
lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_755_ = lean_nat_add(v___x_740_, v___y_754_);
lean_dec(v___y_754_);
lean_dec(v___x_740_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 4, v_l_731_);
lean_ctor_set(v___x_710_, 3, v_tree_713_);
lean_ctor_set(v___x_710_, 2, v_v_715_);
lean_ctor_set(v___x_710_, 1, v_k_714_);
lean_ctor_set(v___x_710_, 0, v___x_755_);
v___x_757_ = v___x_710_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_k_714_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_v_715_);
lean_ctor_set(v_reuseFailAlloc_761_, 3, v_tree_713_);
lean_ctor_set(v_reuseFailAlloc_761_, 4, v_l_731_);
v___x_757_ = v_reuseFailAlloc_761_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_758_; 
v___x_758_ = lean_nat_add(v___x_707_, v_size_733_);
if (lean_obj_tag(v_r_732_) == 0)
{
lean_object* v_size_759_; 
v_size_759_ = lean_ctor_get(v_r_732_, 0);
lean_inc(v_size_759_);
v___y_743_ = v___x_758_;
v___y_744_ = v___x_757_;
v___y_745_ = v_size_759_;
goto v___jp_742_;
}
else
{
lean_object* v___x_760_; 
v___x_760_ = lean_unsigned_to_nat(0u);
v___y_743_ = v___x_758_;
v___y_744_ = v___x_757_;
v___y_745_ = v___x_760_;
goto v___jp_742_;
}
}
}
}
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_770_ = lean_nat_add(v___x_707_, v_size_716_);
v___x_771_ = lean_nat_add(v___x_770_, v_size_702_);
lean_dec(v_size_702_);
v___x_772_ = lean_nat_add(v___x_770_, v_size_728_);
lean_dec(v___x_770_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 4, v_l_705_);
lean_ctor_set(v___x_726_, 3, v_tree_713_);
lean_ctor_set(v___x_726_, 2, v_v_715_);
lean_ctor_set(v___x_726_, 1, v_k_714_);
lean_ctor_set(v___x_726_, 0, v___x_772_);
v___x_774_ = v___x_726_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_k_714_);
lean_ctor_set(v_reuseFailAlloc_778_, 2, v_v_715_);
lean_ctor_set(v_reuseFailAlloc_778_, 3, v_tree_713_);
lean_ctor_set(v_reuseFailAlloc_778_, 4, v_l_705_);
v___x_774_ = v_reuseFailAlloc_778_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_776_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 4, v_r_706_);
lean_ctor_set(v___x_710_, 3, v___x_774_);
lean_ctor_set(v___x_710_, 2, v_v_704_);
lean_ctor_set(v___x_710_, 1, v_k_703_);
lean_ctor_set(v___x_710_, 0, v___x_771_);
v___x_776_ = v___x_710_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_k_703_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v_v_704_);
lean_ctor_set(v_reuseFailAlloc_777_, 3, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_777_, 4, v_r_706_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
}
else
{
lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_838_; 
lean_inc(v_r_706_);
lean_inc(v_v_704_);
lean_inc(v_k_703_);
lean_inc(v_size_702_);
v_isSharedCheck_838_ = !lean_is_exclusive(v_r_688_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; lean_object* v_unused_840_; lean_object* v_unused_841_; lean_object* v_unused_842_; lean_object* v_unused_843_; 
v_unused_839_ = lean_ctor_get(v_r_688_, 4);
lean_dec(v_unused_839_);
v_unused_840_ = lean_ctor_get(v_r_688_, 3);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v_r_688_, 2);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_r_688_, 1);
lean_dec(v_unused_842_);
v_unused_843_ = lean_ctor_get(v_r_688_, 0);
lean_dec(v_unused_843_);
v___x_786_ = v_r_688_;
v_isShared_787_ = v_isSharedCheck_838_;
goto v_resetjp_785_;
}
else
{
lean_dec(v_r_688_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_838_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
if (lean_obj_tag(v_l_705_) == 0)
{
if (lean_obj_tag(v_r_706_) == 0)
{
lean_object* v_k_788_; lean_object* v_v_789_; lean_object* v_size_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_794_; 
v_k_788_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_k_788_);
v_v_789_ = lean_ctor_get(v___x_712_, 1);
lean_inc(v_v_789_);
lean_dec_ref(v___x_712_);
v_size_790_ = lean_ctor_get(v_l_705_, 0);
v___x_791_ = lean_nat_add(v___x_707_, v_size_702_);
lean_dec(v_size_702_);
v___x_792_ = lean_nat_add(v___x_707_, v_size_790_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 4, v_l_705_);
lean_ctor_set(v___x_786_, 3, v_tree_713_);
lean_ctor_set(v___x_786_, 2, v_v_789_);
lean_ctor_set(v___x_786_, 1, v_k_788_);
lean_ctor_set(v___x_786_, 0, v___x_792_);
v___x_794_ = v___x_786_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_k_788_);
lean_ctor_set(v_reuseFailAlloc_798_, 2, v_v_789_);
lean_ctor_set(v_reuseFailAlloc_798_, 3, v_tree_713_);
lean_ctor_set(v_reuseFailAlloc_798_, 4, v_l_705_);
v___x_794_ = v_reuseFailAlloc_798_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_796_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 4, v_r_706_);
lean_ctor_set(v___x_710_, 3, v___x_794_);
lean_ctor_set(v___x_710_, 2, v_v_704_);
lean_ctor_set(v___x_710_, 1, v_k_703_);
lean_ctor_set(v___x_710_, 0, v___x_791_);
v___x_796_ = v___x_710_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v_k_703_);
lean_ctor_set(v_reuseFailAlloc_797_, 2, v_v_704_);
lean_ctor_set(v_reuseFailAlloc_797_, 3, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_797_, 4, v_r_706_);
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
lean_object* v_k_799_; lean_object* v_v_800_; lean_object* v_k_801_; lean_object* v_v_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_816_; 
lean_dec(v_size_702_);
v_k_799_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_k_799_);
v_v_800_ = lean_ctor_get(v___x_712_, 1);
lean_inc(v_v_800_);
lean_dec_ref(v___x_712_);
v_k_801_ = lean_ctor_get(v_l_705_, 1);
v_v_802_ = lean_ctor_get(v_l_705_, 2);
v_isSharedCheck_816_ = !lean_is_exclusive(v_l_705_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; lean_object* v_unused_818_; lean_object* v_unused_819_; 
v_unused_817_ = lean_ctor_get(v_l_705_, 4);
lean_dec(v_unused_817_);
v_unused_818_ = lean_ctor_get(v_l_705_, 3);
lean_dec(v_unused_818_);
v_unused_819_ = lean_ctor_get(v_l_705_, 0);
lean_dec(v_unused_819_);
v___x_804_ = v_l_705_;
v_isShared_805_ = v_isSharedCheck_816_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_v_802_);
lean_inc(v_k_801_);
lean_dec(v_l_705_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_816_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_806_ = lean_unsigned_to_nat(3u);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 4, v_r_706_);
lean_ctor_set(v___x_804_, 3, v_r_706_);
lean_ctor_set(v___x_804_, 2, v_v_800_);
lean_ctor_set(v___x_804_, 1, v_k_799_);
lean_ctor_set(v___x_804_, 0, v___x_707_);
v___x_808_ = v___x_804_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_k_799_);
lean_ctor_set(v_reuseFailAlloc_815_, 2, v_v_800_);
lean_ctor_set(v_reuseFailAlloc_815_, 3, v_r_706_);
lean_ctor_set(v_reuseFailAlloc_815_, 4, v_r_706_);
v___x_808_ = v_reuseFailAlloc_815_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_810_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 3, v_r_706_);
lean_ctor_set(v___x_786_, 0, v___x_707_);
v___x_810_ = v___x_786_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_k_703_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v_v_704_);
lean_ctor_set(v_reuseFailAlloc_814_, 3, v_r_706_);
lean_ctor_set(v_reuseFailAlloc_814_, 4, v_r_706_);
v___x_810_ = v_reuseFailAlloc_814_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_812_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 4, v___x_810_);
lean_ctor_set(v___x_710_, 3, v___x_808_);
lean_ctor_set(v___x_710_, 2, v_v_802_);
lean_ctor_set(v___x_710_, 1, v_k_801_);
lean_ctor_set(v___x_710_, 0, v___x_806_);
v___x_812_ = v___x_710_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_k_801_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v_v_802_);
lean_ctor_set(v_reuseFailAlloc_813_, 3, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_813_, 4, v___x_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_706_) == 0)
{
lean_object* v_k_820_; lean_object* v_v_821_; lean_object* v___x_822_; lean_object* v___x_824_; 
lean_dec(v_size_702_);
v_k_820_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_k_820_);
v_v_821_ = lean_ctor_get(v___x_712_, 1);
lean_inc(v_v_821_);
lean_dec_ref(v___x_712_);
v___x_822_ = lean_unsigned_to_nat(3u);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 4, v_l_705_);
lean_ctor_set(v___x_786_, 2, v_v_821_);
lean_ctor_set(v___x_786_, 1, v_k_820_);
lean_ctor_set(v___x_786_, 0, v___x_707_);
v___x_824_ = v___x_786_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_k_820_);
lean_ctor_set(v_reuseFailAlloc_828_, 2, v_v_821_);
lean_ctor_set(v_reuseFailAlloc_828_, 3, v_l_705_);
lean_ctor_set(v_reuseFailAlloc_828_, 4, v_l_705_);
v___x_824_ = v_reuseFailAlloc_828_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_object* v___x_826_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 4, v_r_706_);
lean_ctor_set(v___x_710_, 3, v___x_824_);
lean_ctor_set(v___x_710_, 2, v_v_704_);
lean_ctor_set(v___x_710_, 1, v_k_703_);
lean_ctor_set(v___x_710_, 0, v___x_822_);
v___x_826_ = v___x_710_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_822_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_k_703_);
lean_ctor_set(v_reuseFailAlloc_827_, 2, v_v_704_);
lean_ctor_set(v_reuseFailAlloc_827_, 3, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_827_, 4, v_r_706_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
else
{
lean_object* v_k_829_; lean_object* v_v_830_; lean_object* v___x_832_; 
v_k_829_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_k_829_);
v_v_830_ = lean_ctor_get(v___x_712_, 1);
lean_inc(v_v_830_);
lean_dec_ref(v___x_712_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 3, v_r_706_);
v___x_832_ = v___x_786_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_size_702_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_k_703_);
lean_ctor_set(v_reuseFailAlloc_837_, 2, v_v_704_);
lean_ctor_set(v_reuseFailAlloc_837_, 3, v_r_706_);
lean_ctor_set(v_reuseFailAlloc_837_, 4, v_r_706_);
v___x_832_ = v_reuseFailAlloc_837_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_833_ = lean_unsigned_to_nat(2u);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 4, v___x_832_);
lean_ctor_set(v___x_710_, 3, v_r_706_);
lean_ctor_set(v___x_710_, 2, v_v_830_);
lean_ctor_set(v___x_710_, 1, v_k_829_);
lean_ctor_set(v___x_710_, 0, v___x_833_);
v___x_835_ = v___x_710_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_k_829_);
lean_ctor_set(v_reuseFailAlloc_836_, 2, v_v_830_);
lean_ctor_set(v_reuseFailAlloc_836_, 3, v_r_706_);
lean_ctor_set(v_reuseFailAlloc_836_, 4, v___x_832_);
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
}
}
}
}
else
{
lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_1002_; 
lean_inc(v_r_706_);
lean_inc(v_v_704_);
lean_inc(v_k_703_);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_r_688_);
if (v_isSharedCheck_1002_ == 0)
{
lean_object* v_unused_1003_; lean_object* v_unused_1004_; lean_object* v_unused_1005_; lean_object* v_unused_1006_; lean_object* v_unused_1007_; 
v_unused_1003_ = lean_ctor_get(v_r_688_, 4);
lean_dec(v_unused_1003_);
v_unused_1004_ = lean_ctor_get(v_r_688_, 3);
lean_dec(v_unused_1004_);
v_unused_1005_ = lean_ctor_get(v_r_688_, 2);
lean_dec(v_unused_1005_);
v_unused_1006_ = lean_ctor_get(v_r_688_, 1);
lean_dec(v_unused_1006_);
v_unused_1007_ = lean_ctor_get(v_r_688_, 0);
lean_dec(v_unused_1007_);
v___x_851_ = v_r_688_;
v_isShared_852_ = v_isSharedCheck_1002_;
goto v_resetjp_850_;
}
else
{
lean_dec(v_r_688_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_1002_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v_tree_854_; 
v___x_853_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_703_, v_v_704_, v_l_705_, v_r_706_);
v_tree_854_ = lean_ctor_get(v___x_853_, 2);
lean_inc(v_tree_854_);
if (lean_obj_tag(v_tree_854_) == 0)
{
lean_object* v_k_855_; lean_object* v_v_856_; lean_object* v_size_857_; lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v_k_855_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_k_855_);
v_v_856_ = lean_ctor_get(v___x_853_, 1);
lean_inc(v_v_856_);
lean_dec_ref(v___x_853_);
v_size_857_ = lean_ctor_get(v_tree_854_, 0);
v___x_858_ = lean_unsigned_to_nat(3u);
v___x_859_ = lean_nat_mul(v___x_858_, v_size_857_);
v___x_860_ = lean_nat_dec_lt(v___x_859_, v_size_697_);
lean_dec(v___x_859_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
lean_dec(v_r_701_);
v___x_861_ = lean_nat_add(v___x_707_, v_size_697_);
v___x_862_ = lean_nat_add(v___x_861_, v_size_857_);
lean_dec(v___x_861_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 4, v_tree_854_);
lean_ctor_set(v___x_851_, 3, v_l_687_);
lean_ctor_set(v___x_851_, 2, v_v_856_);
lean_ctor_set(v___x_851_, 1, v_k_855_);
lean_ctor_set(v___x_851_, 0, v___x_862_);
v___x_864_ = v___x_851_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_k_855_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v_v_856_);
lean_ctor_set(v_reuseFailAlloc_865_, 3, v_l_687_);
lean_ctor_set(v_reuseFailAlloc_865_, 4, v_tree_854_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
else
{
lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_931_; 
lean_inc(v_l_700_);
lean_inc(v_v_699_);
lean_inc(v_k_698_);
lean_inc(v_size_697_);
v_isSharedCheck_931_ = !lean_is_exclusive(v_l_687_);
if (v_isSharedCheck_931_ == 0)
{
lean_object* v_unused_932_; lean_object* v_unused_933_; lean_object* v_unused_934_; lean_object* v_unused_935_; lean_object* v_unused_936_; 
v_unused_932_ = lean_ctor_get(v_l_687_, 4);
lean_dec(v_unused_932_);
v_unused_933_ = lean_ctor_get(v_l_687_, 3);
lean_dec(v_unused_933_);
v_unused_934_ = lean_ctor_get(v_l_687_, 2);
lean_dec(v_unused_934_);
v_unused_935_ = lean_ctor_get(v_l_687_, 1);
lean_dec(v_unused_935_);
v_unused_936_ = lean_ctor_get(v_l_687_, 0);
lean_dec(v_unused_936_);
v___x_867_ = v_l_687_;
v_isShared_868_ = v_isSharedCheck_931_;
goto v_resetjp_866_;
}
else
{
lean_dec(v_l_687_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_931_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v_size_869_; lean_object* v_size_870_; lean_object* v_k_871_; lean_object* v_v_872_; lean_object* v_l_873_; lean_object* v_r_874_; lean_object* v___x_875_; lean_object* v___x_876_; uint8_t v___x_877_; 
v_size_869_ = lean_ctor_get(v_l_700_, 0);
v_size_870_ = lean_ctor_get(v_r_701_, 0);
v_k_871_ = lean_ctor_get(v_r_701_, 1);
v_v_872_ = lean_ctor_get(v_r_701_, 2);
v_l_873_ = lean_ctor_get(v_r_701_, 3);
v_r_874_ = lean_ctor_get(v_r_701_, 4);
v___x_875_ = lean_unsigned_to_nat(2u);
v___x_876_ = lean_nat_mul(v___x_875_, v_size_869_);
v___x_877_ = lean_nat_dec_lt(v_size_870_, v___x_876_);
lean_dec(v___x_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_915_; 
lean_inc(v_r_874_);
lean_inc(v_l_873_);
lean_inc(v_v_872_);
lean_inc(v_k_871_);
lean_del_object(v___x_867_);
v_isSharedCheck_915_ = !lean_is_exclusive(v_r_701_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; lean_object* v_unused_917_; lean_object* v_unused_918_; lean_object* v_unused_919_; lean_object* v_unused_920_; 
v_unused_916_ = lean_ctor_get(v_r_701_, 4);
lean_dec(v_unused_916_);
v_unused_917_ = lean_ctor_get(v_r_701_, 3);
lean_dec(v_unused_917_);
v_unused_918_ = lean_ctor_get(v_r_701_, 2);
lean_dec(v_unused_918_);
v_unused_919_ = lean_ctor_get(v_r_701_, 1);
lean_dec(v_unused_919_);
v_unused_920_ = lean_ctor_get(v_r_701_, 0);
lean_dec(v_unused_920_);
v___x_879_ = v_r_701_;
v_isShared_880_ = v_isSharedCheck_915_;
goto v_resetjp_878_;
}
else
{
lean_dec(v_r_701_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_915_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___x_903_; lean_object* v___y_905_; 
v___x_881_ = lean_nat_add(v___x_707_, v_size_697_);
lean_dec(v_size_697_);
v___x_882_ = lean_nat_add(v___x_881_, v_size_857_);
lean_dec(v___x_881_);
v___x_903_ = lean_nat_add(v___x_707_, v_size_869_);
if (lean_obj_tag(v_l_873_) == 0)
{
lean_object* v_size_913_; 
v_size_913_ = lean_ctor_get(v_l_873_, 0);
lean_inc(v_size_913_);
v___y_905_ = v_size_913_;
goto v___jp_904_;
}
else
{
lean_object* v___x_914_; 
v___x_914_ = lean_unsigned_to_nat(0u);
v___y_905_ = v___x_914_;
goto v___jp_904_;
}
v___jp_883_:
{
lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_887_ = lean_nat_add(v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec(v___y_885_);
lean_inc_ref(v_tree_854_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 4, v_tree_854_);
lean_ctor_set(v___x_879_, 3, v_r_874_);
lean_ctor_set(v___x_879_, 2, v_v_856_);
lean_ctor_set(v___x_879_, 1, v_k_855_);
lean_ctor_set(v___x_879_, 0, v___x_887_);
v___x_889_ = v___x_879_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_k_855_);
lean_ctor_set(v_reuseFailAlloc_902_, 2, v_v_856_);
lean_ctor_set(v_reuseFailAlloc_902_, 3, v_r_874_);
lean_ctor_set(v_reuseFailAlloc_902_, 4, v_tree_854_);
v___x_889_ = v_reuseFailAlloc_902_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
v_isSharedCheck_896_ = !lean_is_exclusive(v_tree_854_);
if (v_isSharedCheck_896_ == 0)
{
lean_object* v_unused_897_; lean_object* v_unused_898_; lean_object* v_unused_899_; lean_object* v_unused_900_; lean_object* v_unused_901_; 
v_unused_897_ = lean_ctor_get(v_tree_854_, 4);
lean_dec(v_unused_897_);
v_unused_898_ = lean_ctor_get(v_tree_854_, 3);
lean_dec(v_unused_898_);
v_unused_899_ = lean_ctor_get(v_tree_854_, 2);
lean_dec(v_unused_899_);
v_unused_900_ = lean_ctor_get(v_tree_854_, 1);
lean_dec(v_unused_900_);
v_unused_901_ = lean_ctor_get(v_tree_854_, 0);
lean_dec(v_unused_901_);
v___x_891_ = v_tree_854_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_dec(v_tree_854_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 4, v___x_889_);
lean_ctor_set(v___x_891_, 3, v___y_884_);
lean_ctor_set(v___x_891_, 2, v_v_872_);
lean_ctor_set(v___x_891_, 1, v_k_871_);
lean_ctor_set(v___x_891_, 0, v___x_882_);
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_k_871_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_v_872_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v___y_884_);
lean_ctor_set(v_reuseFailAlloc_895_, 4, v___x_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
v___jp_904_:
{
lean_object* v___x_906_; lean_object* v___x_908_; 
v___x_906_ = lean_nat_add(v___x_903_, v___y_905_);
lean_dec(v___y_905_);
lean_dec(v___x_903_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 4, v_l_873_);
lean_ctor_set(v___x_851_, 3, v_l_700_);
lean_ctor_set(v___x_851_, 2, v_v_699_);
lean_ctor_set(v___x_851_, 1, v_k_698_);
lean_ctor_set(v___x_851_, 0, v___x_906_);
v___x_908_ = v___x_851_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_k_698_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_v_699_);
lean_ctor_set(v_reuseFailAlloc_912_, 3, v_l_700_);
lean_ctor_set(v_reuseFailAlloc_912_, 4, v_l_873_);
v___x_908_ = v_reuseFailAlloc_912_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_909_; 
v___x_909_ = lean_nat_add(v___x_707_, v_size_857_);
if (lean_obj_tag(v_r_874_) == 0)
{
lean_object* v_size_910_; 
v_size_910_ = lean_ctor_get(v_r_874_, 0);
lean_inc(v_size_910_);
v___y_884_ = v___x_908_;
v___y_885_ = v___x_909_;
v___y_886_ = v_size_910_;
goto v___jp_883_;
}
else
{
lean_object* v___x_911_; 
v___x_911_ = lean_unsigned_to_nat(0u);
v___y_884_ = v___x_908_;
v___y_885_ = v___x_909_;
v___y_886_ = v___x_911_;
goto v___jp_883_;
}
}
}
}
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_921_ = lean_nat_add(v___x_707_, v_size_697_);
lean_dec(v_size_697_);
v___x_922_ = lean_nat_add(v___x_921_, v_size_857_);
lean_dec(v___x_921_);
v___x_923_ = lean_nat_add(v___x_707_, v_size_857_);
v___x_924_ = lean_nat_add(v___x_923_, v_size_870_);
lean_dec(v___x_923_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 4, v_tree_854_);
lean_ctor_set(v___x_851_, 3, v_r_701_);
lean_ctor_set(v___x_851_, 2, v_v_856_);
lean_ctor_set(v___x_851_, 1, v_k_855_);
lean_ctor_set(v___x_851_, 0, v___x_924_);
v___x_926_ = v___x_851_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_k_855_);
lean_ctor_set(v_reuseFailAlloc_930_, 2, v_v_856_);
lean_ctor_set(v_reuseFailAlloc_930_, 3, v_r_701_);
lean_ctor_set(v_reuseFailAlloc_930_, 4, v_tree_854_);
v___x_926_ = v_reuseFailAlloc_930_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_928_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 4, v___x_926_);
lean_ctor_set(v___x_867_, 0, v___x_922_);
v___x_928_ = v___x_867_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_922_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_k_698_);
lean_ctor_set(v_reuseFailAlloc_929_, 2, v_v_699_);
lean_ctor_set(v_reuseFailAlloc_929_, 3, v_l_700_);
lean_ctor_set(v_reuseFailAlloc_929_, 4, v___x_926_);
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
else
{
if (lean_obj_tag(v_l_700_) == 0)
{
lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_960_; 
lean_inc_ref(v_l_700_);
lean_inc(v_v_699_);
lean_inc(v_k_698_);
lean_inc(v_size_697_);
v_isSharedCheck_960_ = !lean_is_exclusive(v_l_687_);
if (v_isSharedCheck_960_ == 0)
{
lean_object* v_unused_961_; lean_object* v_unused_962_; lean_object* v_unused_963_; lean_object* v_unused_964_; lean_object* v_unused_965_; 
v_unused_961_ = lean_ctor_get(v_l_687_, 4);
lean_dec(v_unused_961_);
v_unused_962_ = lean_ctor_get(v_l_687_, 3);
lean_dec(v_unused_962_);
v_unused_963_ = lean_ctor_get(v_l_687_, 2);
lean_dec(v_unused_963_);
v_unused_964_ = lean_ctor_get(v_l_687_, 1);
lean_dec(v_unused_964_);
v_unused_965_ = lean_ctor_get(v_l_687_, 0);
lean_dec(v_unused_965_);
v___x_938_ = v_l_687_;
v_isShared_939_ = v_isSharedCheck_960_;
goto v_resetjp_937_;
}
else
{
lean_dec(v_l_687_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_960_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
if (lean_obj_tag(v_r_701_) == 0)
{
lean_object* v_k_940_; lean_object* v_v_941_; lean_object* v_size_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v_k_940_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_k_940_);
v_v_941_ = lean_ctor_get(v___x_853_, 1);
lean_inc(v_v_941_);
lean_dec_ref(v___x_853_);
v_size_942_ = lean_ctor_get(v_r_701_, 0);
v___x_943_ = lean_nat_add(v___x_707_, v_size_697_);
lean_dec(v_size_697_);
v___x_944_ = lean_nat_add(v___x_707_, v_size_942_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 4, v_tree_854_);
lean_ctor_set(v___x_851_, 3, v_r_701_);
lean_ctor_set(v___x_851_, 2, v_v_941_);
lean_ctor_set(v___x_851_, 1, v_k_940_);
lean_ctor_set(v___x_851_, 0, v___x_944_);
v___x_946_ = v___x_851_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_k_940_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_v_941_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_r_701_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_tree_854_);
v___x_946_ = v_reuseFailAlloc_950_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; 
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 4, v___x_946_);
lean_ctor_set(v___x_938_, 0, v___x_943_);
v___x_948_ = v___x_938_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_k_698_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_v_699_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v_l_700_);
lean_ctor_set(v_reuseFailAlloc_949_, 4, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
else
{
lean_object* v_k_951_; lean_object* v_v_952_; lean_object* v___x_953_; lean_object* v___x_955_; 
lean_dec(v_size_697_);
v_k_951_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_k_951_);
v_v_952_ = lean_ctor_get(v___x_853_, 1);
lean_inc(v_v_952_);
lean_dec_ref(v___x_853_);
v___x_953_ = lean_unsigned_to_nat(3u);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 4, v_r_701_);
lean_ctor_set(v___x_851_, 3, v_r_701_);
lean_ctor_set(v___x_851_, 2, v_v_952_);
lean_ctor_set(v___x_851_, 1, v_k_951_);
lean_ctor_set(v___x_851_, 0, v___x_707_);
v___x_955_ = v___x_851_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_k_951_);
lean_ctor_set(v_reuseFailAlloc_959_, 2, v_v_952_);
lean_ctor_set(v_reuseFailAlloc_959_, 3, v_r_701_);
lean_ctor_set(v_reuseFailAlloc_959_, 4, v_r_701_);
v___x_955_ = v_reuseFailAlloc_959_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_957_; 
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 4, v___x_955_);
lean_ctor_set(v___x_938_, 0, v___x_953_);
v___x_957_ = v___x_938_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_k_698_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v_v_699_);
lean_ctor_set(v_reuseFailAlloc_958_, 3, v_l_700_);
lean_ctor_set(v_reuseFailAlloc_958_, 4, v___x_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_701_) == 0)
{
lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_990_; 
lean_inc(v_l_700_);
lean_inc(v_v_699_);
lean_inc(v_k_698_);
v_isSharedCheck_990_ = !lean_is_exclusive(v_l_687_);
if (v_isSharedCheck_990_ == 0)
{
lean_object* v_unused_991_; lean_object* v_unused_992_; lean_object* v_unused_993_; lean_object* v_unused_994_; lean_object* v_unused_995_; 
v_unused_991_ = lean_ctor_get(v_l_687_, 4);
lean_dec(v_unused_991_);
v_unused_992_ = lean_ctor_get(v_l_687_, 3);
lean_dec(v_unused_992_);
v_unused_993_ = lean_ctor_get(v_l_687_, 2);
lean_dec(v_unused_993_);
v_unused_994_ = lean_ctor_get(v_l_687_, 1);
lean_dec(v_unused_994_);
v_unused_995_ = lean_ctor_get(v_l_687_, 0);
lean_dec(v_unused_995_);
v___x_967_ = v_l_687_;
v_isShared_968_ = v_isSharedCheck_990_;
goto v_resetjp_966_;
}
else
{
lean_dec(v_l_687_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_990_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v_k_969_; lean_object* v_v_970_; lean_object* v_k_971_; lean_object* v_v_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_986_; 
v_k_969_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_k_969_);
v_v_970_ = lean_ctor_get(v___x_853_, 1);
lean_inc(v_v_970_);
lean_dec_ref(v___x_853_);
v_k_971_ = lean_ctor_get(v_r_701_, 1);
v_v_972_ = lean_ctor_get(v_r_701_, 2);
v_isSharedCheck_986_ = !lean_is_exclusive(v_r_701_);
if (v_isSharedCheck_986_ == 0)
{
lean_object* v_unused_987_; lean_object* v_unused_988_; lean_object* v_unused_989_; 
v_unused_987_ = lean_ctor_get(v_r_701_, 4);
lean_dec(v_unused_987_);
v_unused_988_ = lean_ctor_get(v_r_701_, 3);
lean_dec(v_unused_988_);
v_unused_989_ = lean_ctor_get(v_r_701_, 0);
lean_dec(v_unused_989_);
v___x_974_ = v_r_701_;
v_isShared_975_ = v_isSharedCheck_986_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_v_972_);
lean_inc(v_k_971_);
lean_dec(v_r_701_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_986_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_976_; lean_object* v___x_978_; 
v___x_976_ = lean_unsigned_to_nat(3u);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 4, v_l_700_);
lean_ctor_set(v___x_974_, 3, v_l_700_);
lean_ctor_set(v___x_974_, 2, v_v_699_);
lean_ctor_set(v___x_974_, 1, v_k_698_);
lean_ctor_set(v___x_974_, 0, v___x_707_);
v___x_978_ = v___x_974_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_k_698_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v_v_699_);
lean_ctor_set(v_reuseFailAlloc_985_, 3, v_l_700_);
lean_ctor_set(v_reuseFailAlloc_985_, 4, v_l_700_);
v___x_978_ = v_reuseFailAlloc_985_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_980_; 
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 4, v_l_700_);
lean_ctor_set(v___x_851_, 3, v_l_700_);
lean_ctor_set(v___x_851_, 2, v_v_970_);
lean_ctor_set(v___x_851_, 1, v_k_969_);
lean_ctor_set(v___x_851_, 0, v___x_707_);
v___x_980_ = v___x_851_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_k_969_);
lean_ctor_set(v_reuseFailAlloc_984_, 2, v_v_970_);
lean_ctor_set(v_reuseFailAlloc_984_, 3, v_l_700_);
lean_ctor_set(v_reuseFailAlloc_984_, 4, v_l_700_);
v___x_980_ = v_reuseFailAlloc_984_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_982_; 
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 4, v___x_980_);
lean_ctor_set(v___x_967_, 3, v___x_978_);
lean_ctor_set(v___x_967_, 2, v_v_972_);
lean_ctor_set(v___x_967_, 1, v_k_971_);
lean_ctor_set(v___x_967_, 0, v___x_976_);
v___x_982_ = v___x_967_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_976_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_k_971_);
lean_ctor_set(v_reuseFailAlloc_983_, 2, v_v_972_);
lean_ctor_set(v_reuseFailAlloc_983_, 3, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_983_, 4, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
}
}
else
{
lean_object* v_k_996_; lean_object* v_v_997_; lean_object* v___x_998_; lean_object* v___x_1000_; 
v_k_996_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_k_996_);
v_v_997_ = lean_ctor_get(v___x_853_, 1);
lean_inc(v_v_997_);
lean_dec_ref(v___x_853_);
v___x_998_ = lean_unsigned_to_nat(2u);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 4, v_r_701_);
lean_ctor_set(v___x_851_, 3, v_l_687_);
lean_ctor_set(v___x_851_, 2, v_v_997_);
lean_ctor_set(v___x_851_, 1, v_k_996_);
lean_ctor_set(v___x_851_, 0, v___x_998_);
v___x_1000_ = v___x_851_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_k_996_);
lean_ctor_set(v_reuseFailAlloc_1001_, 2, v_v_997_);
lean_ctor_set(v_reuseFailAlloc_1001_, 3, v_l_687_);
lean_ctor_set(v_reuseFailAlloc_1001_, 4, v_r_701_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
}
}
else
{
return v_l_687_;
}
}
else
{
return v_r_688_;
}
}
else
{
lean_object* v_val_1008_; lean_object* v___x_1010_; 
v_val_1008_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_val_1008_);
lean_dec_ref_known(v___x_696_, 1);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 2, v_val_1008_);
lean_ctor_set(v___x_690_, 1, v_k_682_);
v___x_1010_ = v___x_690_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_size_684_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_k_682_);
lean_ctor_set(v_reuseFailAlloc_1011_, 2, v_val_1008_);
lean_ctor_set(v_reuseFailAlloc_1011_, 3, v_l_687_);
lean_ctor_set(v_reuseFailAlloc_1011_, 4, v_r_688_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
default: 
{
lean_object* v_impl_1012_; lean_object* v___x_1013_; 
lean_del_object(v___x_690_);
lean_dec(v_size_684_);
v_impl_1012_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_681_, v_k_682_, v_r_688_);
v___x_1013_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_685_, v_v_686_, v_l_687_, v_impl_1012_);
return v___x_1013_;
}
}
}
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_box(0);
v___x_1016_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_681_, v___x_1015_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_dec(v_k_682_);
return v_t_683_;
}
else
{
lean_object* v_val_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v_val_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_val_1017_);
lean_dec_ref_known(v___x_1016_, 1);
v___x_1018_ = lean_unsigned_to_nat(1u);
v___x_1019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
lean_ctor_set(v___x_1019_, 1, v_k_682_);
lean_ctor_set(v___x_1019_, 2, v_val_1017_);
lean_ctor_set(v___x_1019_, 3, v_t_683_);
lean_ctor_set(v___x_1019_, 4, v_t_683_);
return v___x_1019_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1020_, lean_object* v_i_1021_, lean_object* v_k_1022_){
_start:
{
lean_object* v___x_1023_; uint8_t v___x_1024_; 
v___x_1023_ = lean_array_get_size(v_keys_1020_);
v___x_1024_ = lean_nat_dec_lt(v_i_1021_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_dec(v_i_1021_);
return v___x_1024_;
}
else
{
lean_object* v_k_x27_1025_; uint8_t v___x_1026_; 
v_k_x27_1025_ = lean_array_fget_borrowed(v_keys_1020_, v_i_1021_);
v___x_1026_ = lean_name_eq(v_k_1022_, v_k_x27_1025_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_unsigned_to_nat(1u);
v___x_1028_ = lean_nat_add(v_i_1021_, v___x_1027_);
lean_dec(v_i_1021_);
v_i_1021_ = v___x_1028_;
goto _start;
}
else
{
lean_dec(v_i_1021_);
return v___x_1024_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1030_, lean_object* v_i_1031_, lean_object* v_k_1032_){
_start:
{
uint8_t v_res_1033_; lean_object* v_r_1034_; 
v_res_1033_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_1030_, v_i_1031_, v_k_1032_);
lean_dec(v_k_1032_);
lean_dec_ref(v_keys_1030_);
v_r_1034_ = lean_box(v_res_1033_);
return v_r_1034_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(lean_object* v_x_1035_, size_t v_x_1036_, lean_object* v_x_1037_){
_start:
{
if (lean_obj_tag(v_x_1035_) == 0)
{
lean_object* v_es_1038_; lean_object* v___x_1039_; size_t v___x_1040_; size_t v___x_1041_; lean_object* v_j_1042_; lean_object* v___x_1043_; 
v_es_1038_ = lean_ctor_get(v_x_1035_, 0);
v___x_1039_ = lean_box(2);
v___x_1040_ = ((size_t)31ULL);
v___x_1041_ = lean_usize_land(v_x_1036_, v___x_1040_);
v_j_1042_ = lean_usize_to_nat(v___x_1041_);
v___x_1043_ = lean_array_get_borrowed(v___x_1039_, v_es_1038_, v_j_1042_);
lean_dec(v_j_1042_);
switch(lean_obj_tag(v___x_1043_))
{
case 0:
{
lean_object* v_key_1044_; uint8_t v___x_1045_; 
v_key_1044_ = lean_ctor_get(v___x_1043_, 0);
v___x_1045_ = lean_name_eq(v_x_1037_, v_key_1044_);
return v___x_1045_;
}
case 1:
{
lean_object* v_node_1046_; size_t v___x_1047_; size_t v___x_1048_; 
v_node_1046_ = lean_ctor_get(v___x_1043_, 0);
v___x_1047_ = ((size_t)5ULL);
v___x_1048_ = lean_usize_shift_right(v_x_1036_, v___x_1047_);
v_x_1035_ = v_node_1046_;
v_x_1036_ = v___x_1048_;
goto _start;
}
default: 
{
uint8_t v___x_1050_; 
v___x_1050_ = 0;
return v___x_1050_;
}
}
}
else
{
lean_object* v_ks_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
v_ks_1051_ = lean_ctor_get(v_x_1035_, 0);
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_ks_1051_, v___x_1052_, v_x_1037_);
return v___x_1053_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___boxed(lean_object* v_x_1054_, lean_object* v_x_1055_, lean_object* v_x_1056_){
_start:
{
size_t v_x_3822__boxed_1057_; uint8_t v_res_1058_; lean_object* v_r_1059_; 
v_x_3822__boxed_1057_ = lean_unbox_usize(v_x_1055_);
lean_dec(v_x_1055_);
v_res_1058_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1054_, v_x_3822__boxed_1057_, v_x_1056_);
lean_dec(v_x_1056_);
lean_dec_ref(v_x_1054_);
v_r_1059_ = lean_box(v_res_1058_);
return v_r_1059_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(lean_object* v_x_1060_, lean_object* v_x_1061_){
_start:
{
uint64_t v___y_1063_; 
if (lean_obj_tag(v_x_1061_) == 0)
{
uint64_t v___x_1066_; 
v___x_1066_ = 1723ULL;
v___y_1063_ = v___x_1066_;
goto v___jp_1062_;
}
else
{
uint64_t v_hash_1067_; 
v_hash_1067_ = lean_ctor_get_uint64(v_x_1061_, sizeof(void*)*2);
v___y_1063_ = v_hash_1067_;
goto v___jp_1062_;
}
v___jp_1062_:
{
size_t v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = lean_uint64_to_usize(v___y_1063_);
v___x_1065_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1060_, v___x_1064_, v_x_1061_);
return v___x_1065_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(lean_object* v_x_1068_, lean_object* v_x_1069_){
_start:
{
uint8_t v_res_1070_; lean_object* v_r_1071_; 
v_res_1070_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_1068_, v_x_1069_);
lean_dec(v_x_1069_);
lean_dec_ref(v_x_1068_);
v_r_1071_ = lean_box(v_res_1070_);
return v_r_1071_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(lean_object* v_tactics_1072_, lean_object* v_a_1073_, uint8_t v___x_1074_, lean_object* v_x_1075_, lean_object* v_____s_1076_){
_start:
{
lean_object* v_fst_1077_; lean_object* v_kinds_1078_; uint8_t v___x_1079_; 
v_fst_1077_ = lean_ctor_get(v_x_1075_, 0);
lean_inc(v_fst_1077_);
lean_dec_ref(v_x_1075_);
v_kinds_1078_ = lean_ctor_get(v_tactics_1072_, 1);
v___x_1079_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_kinds_1078_, v_fst_1077_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; 
lean_dec(v_fst_1077_);
lean_dec(v_a_1073_);
v___x_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1080_, 0, v_____s_1076_);
return v___x_1080_;
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1081_ = l_Lean_Name_toString(v_a_1073_, v___x_1074_);
v___x_1082_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1081_, v_fst_1077_, v_____s_1076_);
v___x_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
return v___x_1083_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(lean_object* v_tactics_1084_, lean_object* v_a_1085_, lean_object* v___x_1086_, lean_object* v_x_1087_, lean_object* v_____s_1088_){
_start:
{
uint8_t v___x_3878__boxed_1089_; lean_object* v_res_1090_; 
v___x_3878__boxed_1089_ = lean_unbox(v___x_1086_);
v_res_1090_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(v_tactics_1084_, v_a_1085_, v___x_3878__boxed_1089_, v_x_1087_, v_____s_1088_);
lean_dec_ref(v_tactics_1084_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_f_1091_, lean_object* v_keys_1092_, lean_object* v_vals_1093_, lean_object* v_i_1094_, lean_object* v_acc_1095_){
_start:
{
lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1096_ = lean_array_get_size(v_keys_1092_);
v___x_1097_ = lean_nat_dec_lt(v_i_1094_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; 
lean_dec(v_i_1094_);
lean_dec_ref(v_f_1091_);
v___x_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1098_, 0, v_acc_1095_);
return v___x_1098_;
}
else
{
lean_object* v_k_1099_; lean_object* v_v_1100_; lean_object* v___x_1101_; 
v_k_1099_ = lean_array_fget_borrowed(v_keys_1092_, v_i_1094_);
v_v_1100_ = lean_array_fget_borrowed(v_vals_1093_, v_i_1094_);
lean_inc_ref(v_f_1091_);
lean_inc(v_v_1100_);
lean_inc(v_k_1099_);
v___x_1101_ = lean_apply_3(v_f_1091_, v_acc_1095_, v_k_1099_, v_v_1100_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_dec(v_i_1094_);
lean_dec_ref(v_f_1091_);
return v___x_1101_;
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref_known(v___x_1101_, 1);
v___x_1103_ = lean_unsigned_to_nat(1u);
v___x_1104_ = lean_nat_add(v_i_1094_, v___x_1103_);
lean_dec(v_i_1094_);
v_i_1094_ = v___x_1104_;
v_acc_1095_ = v_a_1102_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_f_1106_, lean_object* v_keys_1107_, lean_object* v_vals_1108_, lean_object* v_i_1109_, lean_object* v_acc_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1106_, v_keys_1107_, v_vals_1108_, v_i_1109_, v_acc_1110_);
lean_dec_ref(v_vals_1108_);
lean_dec_ref(v_keys_1107_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_f_1112_, lean_object* v_as_1113_, size_t v_i_1114_, size_t v_stop_1115_, lean_object* v_b_1116_){
_start:
{
lean_object* v_a_1118_; lean_object* v___y_1123_; uint8_t v___x_1125_; 
v___x_1125_ = lean_usize_dec_eq(v_i_1114_, v_stop_1115_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_array_uget_borrowed(v_as_1113_, v_i_1114_);
switch(lean_obj_tag(v___x_1126_))
{
case 0:
{
lean_object* v_key_1127_; lean_object* v_val_1128_; lean_object* v___x_1129_; 
v_key_1127_ = lean_ctor_get(v___x_1126_, 0);
v_val_1128_ = lean_ctor_get(v___x_1126_, 1);
lean_inc_ref(v_f_1112_);
lean_inc(v_val_1128_);
lean_inc(v_key_1127_);
v___x_1129_ = lean_apply_3(v_f_1112_, v_b_1116_, v_key_1127_, v_val_1128_);
v___y_1123_ = v___x_1129_;
goto v___jp_1122_;
}
case 1:
{
lean_object* v_node_1130_; lean_object* v___x_1131_; 
v_node_1130_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_node_1130_);
lean_inc_ref(v_f_1112_);
v___x_1131_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1112_, v_node_1130_, v_b_1116_);
v___y_1123_ = v___x_1131_;
goto v___jp_1122_;
}
default: 
{
v_a_1118_ = v_b_1116_;
goto v___jp_1117_;
}
}
}
else
{
lean_object* v___x_1132_; 
lean_dec_ref(v_f_1112_);
v___x_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1132_, 0, v_b_1116_);
return v___x_1132_;
}
v___jp_1117_:
{
size_t v___x_1119_; size_t v___x_1120_; 
v___x_1119_ = ((size_t)1ULL);
v___x_1120_ = lean_usize_add(v_i_1114_, v___x_1119_);
v_i_1114_ = v___x_1120_;
v_b_1116_ = v_a_1118_;
goto _start;
}
v___jp_1122_:
{
if (lean_obj_tag(v___y_1123_) == 0)
{
lean_dec_ref(v_f_1112_);
return v___y_1123_;
}
else
{
lean_object* v_a_1124_; 
v_a_1124_ = lean_ctor_get(v___y_1123_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v___y_1123_, 1);
v_a_1118_ = v_a_1124_;
goto v___jp_1117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object* v_f_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_){
_start:
{
if (lean_obj_tag(v_x_1134_) == 0)
{
lean_object* v_es_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1149_; 
v_es_1136_ = lean_ctor_get(v_x_1134_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_x_1134_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1138_ = v_x_1134_;
v_isShared_1139_ = v_isSharedCheck_1149_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_es_1136_);
lean_dec(v_x_1134_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1149_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1140_ = lean_unsigned_to_nat(0u);
v___x_1141_ = lean_array_get_size(v_es_1136_);
v___x_1142_ = lean_nat_dec_lt(v___x_1140_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1144_; 
lean_dec_ref(v_es_1136_);
lean_dec_ref(v_f_1133_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set_tag(v___x_1138_, 1);
lean_ctor_set(v___x_1138_, 0, v_x_1135_);
v___x_1144_ = v___x_1138_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_x_1135_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
else
{
size_t v___x_1146_; size_t v___x_1147_; lean_object* v___x_1148_; 
lean_del_object(v___x_1138_);
v___x_1146_ = ((size_t)0ULL);
v___x_1147_ = lean_usize_of_nat(v___x_1141_);
v___x_1148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1133_, v_es_1136_, v___x_1146_, v___x_1147_, v_x_1135_);
lean_dec_ref(v_es_1136_);
return v___x_1148_;
}
}
}
else
{
lean_object* v_ks_1150_; lean_object* v_vs_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v_ks_1150_ = lean_ctor_get(v_x_1134_, 0);
lean_inc_ref(v_ks_1150_);
v_vs_1151_ = lean_ctor_get(v_x_1134_, 1);
lean_inc_ref(v_vs_1151_);
lean_dec_ref_known(v_x_1134_, 2);
v___x_1152_ = lean_unsigned_to_nat(0u);
v___x_1153_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1133_, v_ks_1150_, v_vs_1151_, v___x_1152_, v_x_1135_);
lean_dec_ref(v_vs_1151_);
lean_dec_ref(v_ks_1150_);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_f_1154_, lean_object* v_as_1155_, lean_object* v_i_1156_, lean_object* v_stop_1157_, lean_object* v_b_1158_){
_start:
{
size_t v_i_boxed_1159_; size_t v_stop_boxed_1160_; lean_object* v_res_1161_; 
v_i_boxed_1159_ = lean_unbox_usize(v_i_1156_);
lean_dec(v_i_1156_);
v_stop_boxed_1160_ = lean_unbox_usize(v_stop_1157_);
lean_dec(v_stop_1157_);
v_res_1161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1154_, v_as_1155_, v_i_boxed_1159_, v_stop_boxed_1160_, v_b_1158_);
lean_dec_ref(v_as_1155_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0(lean_object* v_f_1162_, lean_object* v_s_1163_, lean_object* v_a_1164_, lean_object* v_b_1165_){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1166_, 0, v_a_1164_);
lean_ctor_set(v___x_1166_, 1, v_b_1165_);
v___x_1167_ = lean_apply_2(v_f_1162_, v___x_1166_, v_s_1163_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1167_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1167_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
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
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
v_a_1176_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1167_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1167_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(lean_object* v_map_1184_, lean_object* v_init_1185_, lean_object* v_f_1186_){
_start:
{
lean_object* v___f_1187_; lean_object* v___x_1188_; lean_object* v_a_1189_; 
v___f_1187_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1187_, 0, v_f_1186_);
lean_inc_ref(v_map_1184_);
v___x_1188_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v___f_1187_, v_map_1184_, v_init_1185_);
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1189_);
lean_dec_ref(v___x_1188_);
return v_a_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___boxed(lean_object* v_map_1190_, lean_object* v_init_1191_, lean_object* v_f_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_1190_, v_init_1191_, v_f_1192_);
lean_dec_ref(v_map_1190_);
return v_res_1193_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1194_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0);
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(lean_object* v_tactics_1197_, lean_object* v_a_1198_, uint8_t v___x_1199_, lean_object* v_as_x27_1200_, lean_object* v_b_1201_){
_start:
{
if (lean_obj_tag(v_as_x27_1200_) == 0)
{
lean_dec(v_a_1198_);
lean_dec_ref(v_tactics_1197_);
return v_b_1201_;
}
else
{
lean_object* v_head_1202_; lean_object* v_fst_1203_; lean_object* v_info_1204_; lean_object* v_tail_1205_; lean_object* v_collectKinds_1206_; lean_object* v___x_1207_; lean_object* v___f_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v_head_1202_ = lean_ctor_get(v_as_x27_1200_, 0);
v_fst_1203_ = lean_ctor_get(v_head_1202_, 0);
v_info_1204_ = lean_ctor_get(v_fst_1203_, 0);
v_tail_1205_ = lean_ctor_get(v_as_x27_1200_, 1);
v_collectKinds_1206_ = lean_ctor_get(v_info_1204_, 1);
v___x_1207_ = lean_box(v___x_1199_);
lean_inc(v_a_1198_);
lean_inc_ref(v_tactics_1197_);
v___f_1208_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1208_, 0, v_tactics_1197_);
lean_closure_set(v___f_1208_, 1, v_a_1198_);
lean_closure_set(v___f_1208_, 2, v___x_1207_);
v___x_1209_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1);
lean_inc_ref(v_collectKinds_1206_);
v___x_1210_ = lean_apply_1(v_collectKinds_1206_, v___x_1209_);
v___x_1211_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v___x_1210_, v_b_1201_, v___f_1208_);
lean_dec_ref(v___x_1210_);
v_as_x27_1200_ = v_tail_1205_;
v_b_1201_ = v___x_1211_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(lean_object* v_tactics_1213_, lean_object* v_a_1214_, lean_object* v___x_1215_, lean_object* v_as_x27_1216_, lean_object* v_b_1217_){
_start:
{
uint8_t v___x_4038__boxed_1218_; lean_object* v_res_1219_; 
v___x_4038__boxed_1218_ = lean_unbox(v___x_1215_);
v_res_1219_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1213_, v_a_1214_, v___x_4038__boxed_1218_, v_as_x27_1216_, v_b_1217_);
lean_dec(v_as_x27_1216_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(lean_object* v_tactics_1223_, lean_object* v_init_1224_, lean_object* v_x_1225_){
_start:
{
if (lean_obj_tag(v_x_1225_) == 0)
{
lean_object* v_k_1226_; lean_object* v_v_1227_; lean_object* v_l_1228_; lean_object* v_r_1229_; lean_object* v___x_1230_; lean_object* v_a_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v_k_1226_ = lean_ctor_get(v_x_1225_, 1);
lean_inc(v_k_1226_);
v_v_1227_ = lean_ctor_get(v_x_1225_, 2);
lean_inc(v_v_1227_);
v_l_1228_ = lean_ctor_get(v_x_1225_, 3);
lean_inc(v_l_1228_);
v_r_1229_ = lean_ctor_get(v_x_1225_, 4);
lean_inc(v_r_1229_);
lean_dec_ref_known(v_x_1225_, 5);
lean_inc_ref(v_tactics_1223_);
v___x_1230_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_1223_, v_init_1224_, v_l_1228_);
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1231_);
v___x_1232_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1));
v___x_1233_ = lean_name_eq(v_k_1226_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; 
lean_dec_ref(v___x_1230_);
lean_inc_ref(v_tactics_1223_);
v___x_1234_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1223_, v_k_1226_, v___x_1233_, v_v_1227_, v_a_1231_);
lean_dec(v_v_1227_);
v_init_1224_ = v___x_1234_;
v_x_1225_ = v_r_1229_;
goto _start;
}
else
{
lean_object* v_a_1236_; 
lean_dec(v_a_1231_);
lean_dec(v_v_1227_);
lean_dec(v_k_1226_);
v_a_1236_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1236_);
lean_dec_ref(v___x_1230_);
v_init_1224_ = v_a_1236_;
v_x_1225_ = v_r_1229_;
goto _start;
}
}
else
{
lean_object* v___x_1238_; 
lean_dec_ref(v_tactics_1223_);
v___x_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1238_, 0, v_init_1224_);
return v___x_1238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(lean_object* v_tactics_1239_, lean_object* v_table_1240_, lean_object* v_firsts_1241_){
_start:
{
lean_object* v___x_1242_; lean_object* v_a_1243_; 
v___x_1242_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_1239_, v_firsts_1241_, v_table_1240_);
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
lean_dec_ref(v___x_1242_);
return v_a_1243_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_object* v_00_u03b2_1244_, lean_object* v_x_1245_, lean_object* v_x_1246_){
_start:
{
uint8_t v___x_1247_; 
v___x_1247_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_1245_, v_x_1246_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(lean_object* v_00_u03b2_1248_, lean_object* v_x_1249_, lean_object* v_x_1250_){
_start:
{
uint8_t v_res_1251_; lean_object* v_r_1252_; 
v_res_1251_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(v_00_u03b2_1248_, v_x_1249_, v_x_1250_);
lean_dec(v_x_1250_);
lean_dec_ref(v_x_1249_);
v_r_1252_ = lean_box(v_res_1251_);
return v_r_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(lean_object* v___x_1253_, lean_object* v_k_1254_, lean_object* v_t_1255_, lean_object* v_hl_1256_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1253_, v_k_1254_, v_t_1255_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(lean_object* v_00_u03c3_1258_, lean_object* v_00_u03b2_1259_, lean_object* v_map_1260_, lean_object* v_init_1261_, lean_object* v_f_1262_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_1260_, v_init_1261_, v_f_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___boxed(lean_object* v_00_u03c3_1264_, lean_object* v_00_u03b2_1265_, lean_object* v_map_1266_, lean_object* v_init_1267_, lean_object* v_f_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(v_00_u03c3_1264_, v_00_u03b2_1265_, v_map_1266_, v_init_1267_, v_f_1268_);
lean_dec_ref(v_map_1266_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(lean_object* v_tactics_1270_, lean_object* v_a_1271_, uint8_t v___x_1272_, lean_object* v_as_1273_, lean_object* v_as_x27_1274_, lean_object* v_b_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1270_, v_a_1271_, v___x_1272_, v_as_x27_1274_, v_b_1275_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(lean_object* v_tactics_1278_, lean_object* v_a_1279_, lean_object* v___x_1280_, lean_object* v_as_1281_, lean_object* v_as_x27_1282_, lean_object* v_b_1283_, lean_object* v_a_1284_){
_start:
{
uint8_t v___x_4121__boxed_1285_; lean_object* v_res_1286_; 
v___x_4121__boxed_1285_ = lean_unbox(v___x_1280_);
v_res_1286_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(v_tactics_1278_, v_a_1279_, v___x_4121__boxed_1285_, v_as_1281_, v_as_x27_1282_, v_b_1283_, v_a_1284_);
lean_dec(v_as_x27_1282_);
lean_dec(v_as_1281_);
return v_res_1286_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_object* v_00_u03b2_1287_, lean_object* v_x_1288_, size_t v_x_1289_, lean_object* v_x_1290_){
_start:
{
uint8_t v___x_1291_; 
v___x_1291_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1288_, v_x_1289_, v_x_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1292_, lean_object* v_x_1293_, lean_object* v_x_1294_, lean_object* v_x_1295_){
_start:
{
size_t v_x_4130__boxed_1296_; uint8_t v_res_1297_; lean_object* v_r_1298_; 
v_x_4130__boxed_1296_ = lean_unbox_usize(v_x_1294_);
lean_dec(v_x_1294_);
v_res_1297_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(v_00_u03b2_1292_, v_x_1293_, v_x_4130__boxed_1296_, v_x_1295_);
lean_dec(v_x_1295_);
lean_dec_ref(v_x_1293_);
v_r_1298_ = lean_box(v_res_1297_);
return v_r_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(lean_object* v_map_1299_, lean_object* v_f_1300_, lean_object* v_init_1301_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1300_, v_map_1299_, v_init_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(lean_object* v_00_u03c3_1303_, lean_object* v_00_u03c3_1304_, lean_object* v_00_u03b2_1305_, lean_object* v_map_1306_, lean_object* v_f_1307_, lean_object* v_init_1308_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1307_, v_map_1306_, v_init_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1310_, lean_object* v_keys_1311_, lean_object* v_vals_1312_, lean_object* v_heq_1313_, lean_object* v_i_1314_, lean_object* v_k_1315_){
_start:
{
uint8_t v___x_1316_; 
v___x_1316_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_1311_, v_i_1314_, v_k_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1317_, lean_object* v_keys_1318_, lean_object* v_vals_1319_, lean_object* v_heq_1320_, lean_object* v_i_1321_, lean_object* v_k_1322_){
_start:
{
uint8_t v_res_1323_; lean_object* v_r_1324_; 
v_res_1323_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(v_00_u03b2_1317_, v_keys_1318_, v_vals_1319_, v_heq_1320_, v_i_1321_, v_k_1322_);
lean_dec(v_k_1322_);
lean_dec_ref(v_vals_1319_);
lean_dec_ref(v_keys_1318_);
v_r_1324_ = lean_box(v_res_1323_);
return v_r_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(lean_object* v_00_u03c3_1325_, lean_object* v_00_u03c3_1326_, lean_object* v_00_u03b1_1327_, lean_object* v_00_u03b2_1328_, lean_object* v_f_1329_, lean_object* v_x_1330_, lean_object* v_x_1331_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1329_, v_x_1330_, v_x_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b1_1333_, lean_object* v_00_u03b2_1334_, lean_object* v_00_u03c3_1335_, lean_object* v_00_u03c3_1336_, lean_object* v_f_1337_, lean_object* v_as_1338_, size_t v_i_1339_, size_t v_stop_1340_, lean_object* v_b_1341_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1337_, v_as_1338_, v_i_1339_, v_stop_1340_, v_b_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1343_, lean_object* v_00_u03b2_1344_, lean_object* v_00_u03c3_1345_, lean_object* v_00_u03c3_1346_, lean_object* v_f_1347_, lean_object* v_as_1348_, lean_object* v_i_1349_, lean_object* v_stop_1350_, lean_object* v_b_1351_){
_start:
{
size_t v_i_boxed_1352_; size_t v_stop_boxed_1353_; lean_object* v_res_1354_; 
v_i_boxed_1352_ = lean_unbox_usize(v_i_1349_);
lean_dec(v_i_1349_);
v_stop_boxed_1353_ = lean_unbox_usize(v_stop_1350_);
lean_dec(v_stop_1350_);
v_res_1354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(v_00_u03b1_1343_, v_00_u03b2_1344_, v_00_u03c3_1345_, v_00_u03c3_1346_, v_f_1347_, v_as_1348_, v_i_boxed_1352_, v_stop_boxed_1353_, v_b_1351_);
lean_dec_ref(v_as_1348_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03c3_1355_, lean_object* v_00_u03c3_1356_, lean_object* v_00_u03b1_1357_, lean_object* v_00_u03b2_1358_, lean_object* v_f_1359_, lean_object* v_keys_1360_, lean_object* v_vals_1361_, lean_object* v_heq_1362_, lean_object* v_i_1363_, lean_object* v_acc_1364_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1359_, v_keys_1360_, v_vals_1361_, v_i_1363_, v_acc_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03c3_1366_, lean_object* v_00_u03c3_1367_, lean_object* v_00_u03b1_1368_, lean_object* v_00_u03b2_1369_, lean_object* v_f_1370_, lean_object* v_keys_1371_, lean_object* v_vals_1372_, lean_object* v_heq_1373_, lean_object* v_i_1374_, lean_object* v_acc_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(v_00_u03c3_1366_, v_00_u03c3_1367_, v_00_u03b1_1368_, v_00_u03b2_1369_, v_f_1370_, v_keys_1371_, v_vals_1372_, v_heq_1373_, v_i_1374_, v_acc_1375_);
lean_dec_ref(v_vals_1372_);
lean_dec_ref(v_keys_1371_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(lean_object* v_x1_1377_, lean_object* v_x2_1378_){
_start:
{
lean_object* v_fst_1379_; lean_object* v_snd_1380_; lean_object* v___x_1381_; 
v_fst_1379_ = lean_ctor_get(v_x2_1378_, 0);
lean_inc(v_fst_1379_);
v_snd_1380_ = lean_ctor_get(v_x2_1378_, 1);
lean_inc(v_snd_1380_);
lean_dec_ref(v_x2_1378_);
v___x_1381_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1379_, v_snd_1380_, v_x1_1377_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(lean_object* v___f_1401_, lean_object* v_x1_1402_, lean_object* v_x2_1403_){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1404_ = lean_unsigned_to_nat(0u);
v___x_1405_ = lean_array_get_size(v_x2_1403_);
v___x_1406_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_1407_ = lean_nat_dec_lt(v___x_1404_, v___x_1405_);
if (v___x_1407_ == 0)
{
lean_dec_ref(v_x2_1403_);
lean_dec_ref(v___f_1401_);
return v_x1_1402_;
}
else
{
uint8_t v___x_1408_; 
v___x_1408_ = lean_nat_dec_le(v___x_1405_, v___x_1405_);
if (v___x_1408_ == 0)
{
if (v___x_1407_ == 0)
{
lean_dec_ref(v_x2_1403_);
lean_dec_ref(v___f_1401_);
return v_x1_1402_;
}
else
{
size_t v___x_1409_; size_t v___x_1410_; lean_object* v___x_1411_; 
v___x_1409_ = ((size_t)0ULL);
v___x_1410_ = lean_usize_of_nat(v___x_1405_);
v___x_1411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1406_, v___f_1401_, v_x2_1403_, v___x_1409_, v___x_1410_, v_x1_1402_);
return v___x_1411_;
}
}
else
{
size_t v___x_1412_; size_t v___x_1413_; lean_object* v___x_1414_; 
v___x_1412_ = ((size_t)0ULL);
v___x_1413_ = lean_usize_of_nat(v___x_1405_);
v___x_1414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1406_, v___f_1401_, v_x2_1403_, v___x_1412_, v___x_1413_, v_x1_1402_);
return v___x_1414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object* v___x_1418_, lean_object* v___x_1419_, lean_object* v___x_1420_, lean_object* v___x_1421_, lean_object* v___x_1422_, lean_object* v_toPure_1423_, lean_object* v___f_1424_, lean_object* v_env_1425_){
_start:
{
lean_object* v___x_1426_; lean_object* v_ext_1427_; lean_object* v_toEnvExtension_1428_; lean_object* v_asyncMode_1429_; lean_object* v___x_1430_; lean_object* v_categories_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1426_ = l_Lean_Parser_parserExtension;
v_ext_1427_ = lean_ctor_get(v___x_1426_, 1);
v_toEnvExtension_1428_ = lean_ctor_get(v_ext_1427_, 0);
v_asyncMode_1429_ = lean_ctor_get(v_toEnvExtension_1428_, 2);
lean_inc_ref(v_env_1425_);
v___x_1430_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1418_, v___x_1426_, v_env_1425_, v_asyncMode_1429_);
v_categories_1431_ = lean_ctor_get(v___x_1430_, 2);
lean_inc_ref(v_categories_1431_);
lean_dec(v___x_1430_);
v___x_1432_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_1433_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_1419_, v___x_1420_, v_categories_1431_, v___x_1432_);
lean_dec_ref(v_categories_1431_);
if (lean_obj_tag(v___x_1433_) == 1)
{
lean_object* v_val_1434_; lean_object* v___y_1436_; lean_object* v___x_1443_; lean_object* v_toEnvExtension_1444_; lean_object* v_exportEntriesFn_1445_; lean_object* v_asyncMode_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v_importedEntries_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v_exported_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; 
v_val_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_val_1434_);
lean_dec_ref_known(v___x_1433_, 1);
v___x_1443_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1444_ = lean_ctor_get(v___x_1443_, 0);
v_exportEntriesFn_1445_ = lean_ctor_get(v___x_1443_, 4);
v_asyncMode_1446_ = lean_ctor_get(v_toEnvExtension_1444_, 2);
v___x_1447_ = lean_box(0);
lean_inc_ref_n(v_env_1425_, 2);
v___x_1448_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1421_, v_toEnvExtension_1444_, v_env_1425_, v_asyncMode_1446_, v___x_1447_);
v_importedEntries_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc_ref(v_importedEntries_1449_);
lean_dec(v___x_1448_);
v___x_1450_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1422_, v___x_1443_, v_env_1425_, v_asyncMode_1446_, v___x_1447_);
lean_inc_ref(v_exportEntriesFn_1445_);
v___x_1451_ = lean_apply_2(v_exportEntriesFn_1445_, v_env_1425_, v___x_1450_);
v_exported_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_exported_1452_);
lean_dec_ref(v___x_1451_);
v___x_1453_ = lean_box(1);
v___x_1454_ = lean_array_push(v_importedEntries_1449_, v_exported_1452_);
v___x_1455_ = lean_unsigned_to_nat(0u);
v___x_1456_ = lean_array_get_size(v___x_1454_);
v___x_1457_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_1458_ = lean_nat_dec_lt(v___x_1455_, v___x_1456_);
if (v___x_1458_ == 0)
{
lean_dec_ref(v___x_1454_);
lean_dec_ref(v___f_1424_);
v___y_1436_ = v___x_1453_;
goto v___jp_1435_;
}
else
{
uint8_t v___x_1459_; 
v___x_1459_ = lean_nat_dec_le(v___x_1456_, v___x_1456_);
if (v___x_1459_ == 0)
{
if (v___x_1458_ == 0)
{
lean_dec_ref(v___x_1454_);
lean_dec_ref(v___f_1424_);
v___y_1436_ = v___x_1453_;
goto v___jp_1435_;
}
else
{
size_t v___x_1460_; size_t v___x_1461_; lean_object* v___x_1462_; 
v___x_1460_ = ((size_t)0ULL);
v___x_1461_ = lean_usize_of_nat(v___x_1456_);
v___x_1462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1457_, v___f_1424_, v___x_1454_, v___x_1460_, v___x_1461_, v___x_1453_);
v___y_1436_ = v___x_1462_;
goto v___jp_1435_;
}
}
else
{
size_t v___x_1463_; size_t v___x_1464_; lean_object* v___x_1465_; 
v___x_1463_ = ((size_t)0ULL);
v___x_1464_ = lean_usize_of_nat(v___x_1456_);
v___x_1465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1457_, v___f_1424_, v___x_1454_, v___x_1463_, v___x_1464_, v___x_1453_);
v___y_1436_ = v___x_1465_;
goto v___jp_1435_;
}
}
v___jp_1435_:
{
lean_object* v_tables_1437_; lean_object* v_leadingTable_1438_; lean_object* v_trailingTable_1439_; lean_object* v_firstTokens_1440_; lean_object* v_firstTokens_1441_; lean_object* v___x_1442_; 
v_tables_1437_ = lean_ctor_get(v_val_1434_, 2);
v_leadingTable_1438_ = lean_ctor_get(v_tables_1437_, 0);
v_trailingTable_1439_ = lean_ctor_get(v_tables_1437_, 2);
lean_inc(v_trailingTable_1439_);
lean_inc(v_leadingTable_1438_);
lean_inc(v_val_1434_);
v_firstTokens_1440_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_1434_, v_leadingTable_1438_, v___y_1436_);
v_firstTokens_1441_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_1434_, v_trailingTable_1439_, v_firstTokens_1440_);
v___x_1442_ = lean_apply_2(v_toPure_1423_, lean_box(0), v_firstTokens_1441_);
return v___x_1442_;
}
}
else
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_dec(v___x_1433_);
lean_dec_ref(v_env_1425_);
lean_dec_ref(v___f_1424_);
lean_dec(v___x_1422_);
v___x_1466_ = lean_box(1);
v___x_1467_ = lean_apply_2(v_toPure_1423_, lean_box(0), v___x_1466_);
return v___x_1467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed(lean_object* v___x_1468_, lean_object* v___x_1469_, lean_object* v___x_1470_, lean_object* v___x_1471_, lean_object* v___x_1472_, lean_object* v_toPure_1473_, lean_object* v___f_1474_, lean_object* v_env_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(v___x_1468_, v___x_1469_, v___x_1470_, v___x_1471_, v___x_1472_, v_toPure_1473_, v___f_1474_, v_env_1475_);
lean_dec_ref(v___x_1471_);
lean_dec_ref(v___x_1468_);
return v_res_1476_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2(void){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = lean_box(1);
v___x_1481_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object* v_inst_1484_, lean_object* v_inst_1485_){
_start:
{
lean_object* v_toApplicative_1486_; lean_object* v_toBind_1487_; lean_object* v_getEnv_1488_; lean_object* v_toPure_1489_; lean_object* v___f_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___f_1496_; lean_object* v___x_1497_; 
v_toApplicative_1486_ = lean_ctor_get(v_inst_1484_, 0);
lean_inc_ref(v_toApplicative_1486_);
v_toBind_1487_ = lean_ctor_get(v_inst_1484_, 1);
lean_inc(v_toBind_1487_);
lean_dec_ref(v_inst_1484_);
v_getEnv_1488_ = lean_ctor_get(v_inst_1485_, 0);
lean_inc(v_getEnv_1488_);
lean_dec_ref(v_inst_1485_);
v_toPure_1489_ = lean_ctor_get(v_toApplicative_1486_, 1);
lean_inc(v_toPure_1489_);
lean_dec_ref(v_toApplicative_1486_);
v___f_1490_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1));
v___x_1491_ = lean_box(1);
v___x_1492_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_1493_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_1494_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___x_1495_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___f_1496_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1496_, 0, v___x_1495_);
lean_closure_set(v___f_1496_, 1, v___x_1493_);
lean_closure_set(v___f_1496_, 2, v___x_1494_);
lean_closure_set(v___f_1496_, 3, v___x_1492_);
lean_closure_set(v___f_1496_, 4, v___x_1491_);
lean_closure_set(v___f_1496_, 5, v_toPure_1489_);
lean_closure_set(v___f_1496_, 6, v___f_1490_);
v___x_1497_ = lean_apply_4(v_toBind_1487_, lean_box(0), lean_box(0), v_getEnv_1488_, v___f_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object* v_m_1498_, lean_object* v_inst_1499_, lean_object* v_inst_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(v_inst_1499_, v_inst_1500_);
return v___x_1501_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1502_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0);
v___x_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
return v___x_1504_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1505_ = lean_box(1);
v___x_1506_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4);
v___x_1507_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1);
v___x_1508_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
lean_ctor_set(v___x_1508_, 1, v___x_1506_);
lean_ctor_set(v___x_1508_, 2, v___x_1505_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object* v_n_1510_, lean_object* v___y_1511_, lean_object* v_toPure_1512_, lean_object* v_firsts_1513_, lean_object* v_____do__lift_1514_){
_start:
{
lean_object* v___y_1516_; lean_object* v_val_1527_; 
if (lean_obj_tag(v_____do__lift_1514_) == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__3));
lean_inc(v_n_1510_);
v___x_1530_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_1529_, v_firsts_1513_, v_n_1510_);
if (lean_obj_tag(v___x_1530_) == 0)
{
uint8_t v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1531_ = 1;
lean_inc(v_n_1510_);
v___x_1532_ = l_Lean_Name_toString(v_n_1510_, v___x_1531_);
v___x_1533_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
v___y_1516_ = v___x_1533_;
goto v___jp_1515_;
}
else
{
lean_object* v_val_1534_; 
v_val_1534_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_val_1534_);
lean_dec_ref_known(v___x_1530_, 1);
v_val_1527_ = v_val_1534_;
goto v___jp_1526_;
}
}
else
{
lean_object* v_val_1535_; 
lean_dec(v_firsts_1513_);
v_val_1535_ = lean_ctor_get(v_____do__lift_1514_, 0);
lean_inc(v_val_1535_);
lean_dec_ref_known(v_____do__lift_1514_, 1);
v_val_1527_ = v_val_1535_;
goto v___jp_1526_;
}
v___jp_1515_:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1517_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8);
v___x_1518_ = l_Lean_Expr_const___override(v_n_1510_, v___y_1511_);
v___x_1519_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2);
v___x_1520_ = lean_box(0);
v___x_1521_ = 0;
v___x_1522_ = l_Lean_MessageData_withExprHover(v___y_1516_, v___x_1518_, v___x_1519_, v___x_1520_, v___x_1520_, v___x_1520_, v___x_1521_);
v___x_1523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1517_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
v___x_1524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
lean_ctor_set(v___x_1524_, 1, v___x_1517_);
v___x_1525_ = lean_apply_2(v_toPure_1512_, lean_box(0), v___x_1524_);
return v___x_1525_;
}
v___jp_1526_:
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1528_, 0, v_val_1527_);
v___y_1516_ = v___x_1528_;
goto v___jp_1515_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object* v_n_1536_, lean_object* v_toPure_1537_, lean_object* v_firsts_1538_, lean_object* v_inst_1539_, lean_object* v_inst_1540_, lean_object* v_toBind_1541_, lean_object* v___x_1542_, lean_object* v___x_1543_, lean_object* v___f_1544_, lean_object* v_env_1545_){
_start:
{
lean_object* v___y_1547_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = l_Lean_Environment_constants(v_env_1545_);
lean_inc(v_n_1536_);
v___x_1552_ = l_Lean_SMap_find_x3f_x27___redArg(v___x_1542_, v___x_1543_, v___x_1551_, v_n_1536_);
lean_dec_ref(v___x_1551_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v___x_1553_; 
lean_dec_ref(v___f_1544_);
v___x_1553_ = lean_box(0);
v___y_1547_ = v___x_1553_;
goto v___jp_1546_;
}
else
{
lean_object* v_val_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v_val_1554_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_val_1554_);
lean_dec_ref_known(v___x_1552_, 1);
v___x_1555_ = l_Lean_ConstantInfo_levelParams(v_val_1554_);
lean_dec(v_val_1554_);
v___x_1556_ = lean_box(0);
v___x_1557_ = l_List_mapTR_loop___redArg(v___f_1544_, v___x_1555_, v___x_1556_);
v___y_1547_ = v___x_1557_;
goto v___jp_1546_;
}
v___jp_1546_:
{
lean_object* v___f_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
lean_inc(v_n_1536_);
v___f_1548_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1548_, 0, v_n_1536_);
lean_closure_set(v___f_1548_, 1, v___y_1547_);
lean_closure_set(v___f_1548_, 2, v_toPure_1537_);
lean_closure_set(v___f_1548_, 3, v_firsts_1538_);
v___x_1549_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(v_inst_1539_, v_inst_1540_, v_n_1536_);
v___x_1550_ = lean_apply_4(v_toBind_1541_, lean_box(0), lean_box(0), v___x_1549_, v___f_1548_);
return v___x_1550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object* v_inst_1559_, lean_object* v_inst_1560_, lean_object* v_firsts_1561_, lean_object* v_n_1562_){
_start:
{
lean_object* v_toApplicative_1563_; lean_object* v_toBind_1564_; lean_object* v_getEnv_1565_; lean_object* v_toPure_1566_; lean_object* v___f_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___f_1570_; lean_object* v___x_1571_; 
v_toApplicative_1563_ = lean_ctor_get(v_inst_1559_, 0);
v_toBind_1564_ = lean_ctor_get(v_inst_1559_, 1);
lean_inc_n(v_toBind_1564_, 2);
v_getEnv_1565_ = lean_ctor_get(v_inst_1560_, 0);
lean_inc(v_getEnv_1565_);
v_toPure_1566_ = lean_ctor_get(v_toApplicative_1563_, 1);
lean_inc(v_toPure_1566_);
v___f_1567_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0));
v___x_1568_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_1569_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___f_1570_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1570_, 0, v_n_1562_);
lean_closure_set(v___f_1570_, 1, v_toPure_1566_);
lean_closure_set(v___f_1570_, 2, v_firsts_1561_);
lean_closure_set(v___f_1570_, 3, v_inst_1559_);
lean_closure_set(v___f_1570_, 4, v_inst_1560_);
lean_closure_set(v___f_1570_, 5, v_toBind_1564_);
lean_closure_set(v___f_1570_, 6, v___x_1568_);
lean_closure_set(v___f_1570_, 7, v___x_1569_);
lean_closure_set(v___f_1570_, 8, v___f_1567_);
v___x_1571_ = lean_apply_4(v_toBind_1564_, lean_box(0), lean_box(0), v_getEnv_1565_, v___f_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object* v_m_1572_, lean_object* v_inst_1573_, lean_object* v_inst_1574_, lean_object* v_firsts_1575_, lean_object* v_n_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(v_inst_1573_, v_inst_1574_, v_firsts_1575_, v_n_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object* v_s_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0));
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object* v_s_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v_s_1582_);
lean_dec_ref(v_s_1582_);
return v_res_1583_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t v___x_1584_, lean_object* v_x1_1585_, lean_object* v_x2_1586_){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; 
v___x_1587_ = l_Lean_Name_toString(v_x1_1585_, v___x_1584_);
v___x_1588_ = l_Lean_Name_toString(v_x2_1586_, v___x_1584_);
v___x_1589_ = lean_string_dec_lt(v___x_1587_, v___x_1588_);
lean_dec_ref(v___x_1588_);
lean_dec_ref(v___x_1587_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object* v___x_1590_, lean_object* v_x1_1591_, lean_object* v_x2_1592_){
_start:
{
uint8_t v___x_16905__boxed_1593_; uint8_t v_res_1594_; lean_object* v_r_1595_; 
v___x_16905__boxed_1593_ = lean_unbox(v___x_1590_);
v_res_1594_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_16905__boxed_1593_, v_x1_1591_, v_x2_1592_);
v_r_1595_ = lean_box(v_res_1594_);
return v_r_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(lean_object* v_hi_1596_, lean_object* v_pivot_1597_, lean_object* v_as_1598_, lean_object* v_i_1599_, lean_object* v_k_1600_){
_start:
{
uint8_t v___x_1601_; 
v___x_1601_ = lean_nat_dec_lt(v_k_1600_, v_hi_1596_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_dec(v_k_1600_);
lean_dec(v_pivot_1597_);
v___x_1602_ = lean_array_fswap(v_as_1598_, v_i_1599_, v_hi_1596_);
v___x_1603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1603_, 0, v_i_1599_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
return v___x_1603_;
}
else
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1604_ = lean_array_fget_borrowed(v_as_1598_, v_k_1600_);
lean_inc(v___x_1604_);
v___x_1605_ = l_Lean_Name_toString(v___x_1604_, v___x_1601_);
lean_inc(v_pivot_1597_);
v___x_1606_ = l_Lean_Name_toString(v_pivot_1597_, v___x_1601_);
v___x_1607_ = lean_string_dec_lt(v___x_1605_, v___x_1606_);
lean_dec_ref(v___x_1606_);
lean_dec_ref(v___x_1605_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = lean_unsigned_to_nat(1u);
v___x_1609_ = lean_nat_add(v_k_1600_, v___x_1608_);
lean_dec(v_k_1600_);
v_k_1600_ = v___x_1609_;
goto _start;
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1611_ = lean_array_fswap(v_as_1598_, v_i_1599_, v_k_1600_);
v___x_1612_ = lean_unsigned_to_nat(1u);
v___x_1613_ = lean_nat_add(v_i_1599_, v___x_1612_);
lean_dec(v_i_1599_);
v___x_1614_ = lean_nat_add(v_k_1600_, v___x_1612_);
lean_dec(v_k_1600_);
v_as_1598_ = v___x_1611_;
v_i_1599_ = v___x_1613_;
v_k_1600_ = v___x_1614_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg___boxed(lean_object* v_hi_1616_, lean_object* v_pivot_1617_, lean_object* v_as_1618_, lean_object* v_i_1619_, lean_object* v_k_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_1616_, v_pivot_1617_, v_as_1618_, v_i_1619_, v_k_1620_);
lean_dec(v_hi_1616_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object* v_n_1622_, lean_object* v_as_1623_, lean_object* v_lo_1624_, lean_object* v_hi_1625_){
_start:
{
lean_object* v___y_1627_; uint8_t v___x_1637_; 
v___x_1637_ = lean_nat_dec_lt(v_lo_1624_, v_hi_1625_);
if (v___x_1637_ == 0)
{
lean_dec(v_lo_1624_);
return v_as_1623_;
}
else
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v_mid_1640_; lean_object* v___y_1642_; lean_object* v___y_1648_; lean_object* v___x_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1638_ = lean_nat_add(v_lo_1624_, v_hi_1625_);
v___x_1639_ = lean_unsigned_to_nat(1u);
v_mid_1640_ = lean_nat_shiftr(v___x_1638_, v___x_1639_);
lean_dec(v___x_1638_);
v___x_1653_ = lean_array_fget_borrowed(v_as_1623_, v_mid_1640_);
v___x_1654_ = lean_array_fget_borrowed(v_as_1623_, v_lo_1624_);
lean_inc(v___x_1654_);
lean_inc(v___x_1653_);
v___x_1655_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1637_, v___x_1653_, v___x_1654_);
if (v___x_1655_ == 0)
{
v___y_1648_ = v_as_1623_;
goto v___jp_1647_;
}
else
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_array_fswap(v_as_1623_, v_lo_1624_, v_mid_1640_);
v___y_1648_ = v___x_1656_;
goto v___jp_1647_;
}
v___jp_1641_:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1643_ = lean_array_fget_borrowed(v___y_1642_, v_mid_1640_);
v___x_1644_ = lean_array_fget_borrowed(v___y_1642_, v_hi_1625_);
lean_inc(v___x_1644_);
lean_inc(v___x_1643_);
v___x_1645_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1637_, v___x_1643_, v___x_1644_);
if (v___x_1645_ == 0)
{
lean_dec(v_mid_1640_);
v___y_1627_ = v___y_1642_;
goto v___jp_1626_;
}
else
{
lean_object* v___x_1646_; 
v___x_1646_ = lean_array_fswap(v___y_1642_, v_mid_1640_, v_hi_1625_);
lean_dec(v_mid_1640_);
v___y_1627_ = v___x_1646_;
goto v___jp_1626_;
}
}
v___jp_1647_:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; uint8_t v___x_1651_; 
v___x_1649_ = lean_array_fget_borrowed(v___y_1648_, v_hi_1625_);
v___x_1650_ = lean_array_fget_borrowed(v___y_1648_, v_lo_1624_);
lean_inc(v___x_1650_);
lean_inc(v___x_1649_);
v___x_1651_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1637_, v___x_1649_, v___x_1650_);
if (v___x_1651_ == 0)
{
v___y_1642_ = v___y_1648_;
goto v___jp_1641_;
}
else
{
lean_object* v___x_1652_; 
v___x_1652_ = lean_array_fswap(v___y_1648_, v_lo_1624_, v_hi_1625_);
v___y_1642_ = v___x_1652_;
goto v___jp_1641_;
}
}
}
v___jp_1626_:
{
lean_object* v_pivot_1628_; lean_object* v___x_1629_; lean_object* v_fst_1630_; lean_object* v_snd_1631_; uint8_t v___x_1632_; 
v_pivot_1628_ = lean_array_fget(v___y_1627_, v_hi_1625_);
lean_inc_n(v_lo_1624_, 2);
v___x_1629_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_1625_, v_pivot_1628_, v___y_1627_, v_lo_1624_, v_lo_1624_);
v_fst_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_fst_1630_);
v_snd_1631_ = lean_ctor_get(v___x_1629_, 1);
lean_inc(v_snd_1631_);
lean_dec_ref(v___x_1629_);
v___x_1632_ = lean_nat_dec_le(v_hi_1625_, v_fst_1630_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1633_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_1622_, v_snd_1631_, v_lo_1624_, v_fst_1630_);
v___x_1634_ = lean_unsigned_to_nat(1u);
v___x_1635_ = lean_nat_add(v_fst_1630_, v___x_1634_);
lean_dec(v_fst_1630_);
v_as_1623_ = v___x_1633_;
v_lo_1624_ = v___x_1635_;
goto _start;
}
else
{
lean_dec(v_fst_1630_);
lean_dec(v_lo_1624_);
return v_snd_1631_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object* v_n_1657_, lean_object* v_as_1658_, lean_object* v_lo_1659_, lean_object* v_hi_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_1657_, v_as_1658_, v_lo_1659_, v_hi_1660_);
lean_dec(v_hi_1660_);
lean_dec(v_n_1657_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(lean_object* v_init_1662_, lean_object* v_x_1663_){
_start:
{
if (lean_obj_tag(v_x_1663_) == 0)
{
lean_object* v_k_1664_; lean_object* v_l_1665_; lean_object* v_r_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v_k_1664_ = lean_ctor_get(v_x_1663_, 1);
lean_inc(v_k_1664_);
v_l_1665_ = lean_ctor_get(v_x_1663_, 3);
lean_inc(v_l_1665_);
v_r_1666_ = lean_ctor_get(v_x_1663_, 4);
lean_inc(v_r_1666_);
lean_dec_ref_known(v_x_1663_, 5);
v___x_1667_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_1662_, v_l_1665_);
v___x_1668_ = lean_array_push(v___x_1667_, v_k_1664_);
v_init_1662_ = v___x_1668_;
v_x_1663_ = v_r_1666_;
goto _start;
}
else
{
return v_init_1662_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
if (lean_obj_tag(v_a_1670_) == 0)
{
lean_object* v___x_1672_; 
v___x_1672_ = l_List_reverse___redArg(v_a_1671_);
return v___x_1672_;
}
else
{
lean_object* v_head_1673_; lean_object* v_tail_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1683_; 
v_head_1673_ = lean_ctor_get(v_a_1670_, 0);
v_tail_1674_ = lean_ctor_get(v_a_1670_, 1);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_a_1670_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1676_ = v_a_1670_;
v_isShared_1677_ = v_isSharedCheck_1683_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_tail_1674_);
lean_inc(v_head_1673_);
lean_dec(v_a_1670_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1683_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1678_ = l_Lean_Level_param___override(v_head_1673_);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 1, v_a_1671_);
lean_ctor_set(v___x_1676_, 0, v___x_1678_);
v___x_1680_ = v___x_1676_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1678_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_a_1671_);
v___x_1680_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
v_a_1670_ = v_tail_1674_;
v_a_1671_ = v___x_1680_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object* v_x1_1684_, lean_object* v_x2_1685_){
_start:
{
lean_object* v_fst_1686_; lean_object* v_fst_1687_; uint8_t v___x_1688_; 
v_fst_1686_ = lean_ctor_get(v_x1_1684_, 0);
v_fst_1687_ = lean_ctor_get(v_x2_1685_, 0);
v___x_1688_ = l_Lean_Name_quickLt(v_fst_1686_, v_fst_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_x1_1689_, lean_object* v_x2_1690_){
_start:
{
uint8_t v_res_1691_; lean_object* v_r_1692_; 
v_res_1691_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_x1_1689_, v_x2_1690_);
lean_dec_ref(v_x2_1690_);
lean_dec_ref(v_x1_1689_);
v_r_1692_ = lean_box(v_res_1691_);
return v_r_1692_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object* v_as_1693_, lean_object* v_k_1694_, lean_object* v_x_1695_, lean_object* v_x_1696_){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v_m_1699_; lean_object* v_a_1700_; uint8_t v___x_1701_; 
v___x_1697_ = lean_nat_add(v_x_1695_, v_x_1696_);
v___x_1698_ = lean_unsigned_to_nat(1u);
v_m_1699_ = lean_nat_shiftr(v___x_1697_, v___x_1698_);
lean_dec(v___x_1697_);
v_a_1700_ = lean_array_fget_borrowed(v_as_1693_, v_m_1699_);
v___x_1701_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_a_1700_, v_k_1694_);
if (v___x_1701_ == 0)
{
uint8_t v___x_1702_; 
lean_dec(v_x_1696_);
v___x_1702_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_k_1694_, v_a_1700_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; 
lean_dec(v_m_1699_);
lean_dec(v_x_1695_);
lean_inc(v_a_1700_);
v___x_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1703_, 0, v_a_1700_);
return v___x_1703_;
}
else
{
lean_object* v___x_1704_; uint8_t v___x_1705_; lean_object* v___x_1706_; uint8_t v___y_1708_; 
v___x_1704_ = lean_unsigned_to_nat(0u);
v___x_1705_ = lean_nat_dec_eq(v_m_1699_, v___x_1704_);
v___x_1706_ = lean_nat_sub(v_m_1699_, v___x_1698_);
lean_dec(v_m_1699_);
if (v___x_1705_ == 0)
{
uint8_t v___x_1711_; 
v___x_1711_ = lean_nat_dec_lt(v___x_1706_, v_x_1695_);
v___y_1708_ = v___x_1711_;
goto v___jp_1707_;
}
else
{
v___y_1708_ = v___x_1705_;
goto v___jp_1707_;
}
v___jp_1707_:
{
if (v___y_1708_ == 0)
{
v_x_1696_ = v___x_1706_;
goto _start;
}
else
{
lean_object* v___x_1710_; 
lean_dec(v___x_1706_);
lean_dec(v_x_1695_);
v___x_1710_ = lean_box(0);
return v___x_1710_;
}
}
}
}
else
{
lean_object* v___x_1712_; uint8_t v___x_1713_; 
lean_dec(v_x_1695_);
v___x_1712_ = lean_nat_add(v_m_1699_, v___x_1698_);
lean_dec(v_m_1699_);
v___x_1713_ = lean_nat_dec_le(v___x_1712_, v_x_1696_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; 
lean_dec(v___x_1712_);
lean_dec(v_x_1696_);
v___x_1714_ = lean_box(0);
return v___x_1714_;
}
else
{
v_x_1695_ = v___x_1712_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_as_1716_, lean_object* v_k_1717_, lean_object* v_x_1718_, lean_object* v_x_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_1716_, v_k_1717_, v_x_1718_, v_x_1719_);
lean_dec_ref(v_k_1717_);
lean_dec_ref(v_as_1716_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object* v_tac_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v___x_1725_; lean_object* v_env_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1725_ = lean_st_ref_get(v___y_1723_);
v_env_1729_ = lean_ctor_get(v___x_1725_, 0);
lean_inc_ref(v_env_1729_);
lean_dec(v___x_1725_);
v___x_1730_ = lean_box(1);
v___x_1731_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1729_, v_tac_1722_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v___x_1732_; lean_object* v_toEnvExtension_1733_; lean_object* v_asyncMode_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1732_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1733_ = lean_ctor_get(v___x_1732_, 0);
v_asyncMode_1734_ = lean_ctor_get(v_toEnvExtension_1733_, 2);
v___x_1735_ = lean_box(0);
v___x_1736_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1730_, v___x_1732_, v_env_1729_, v_asyncMode_1734_, v___x_1735_);
v___x_1737_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1736_, v_tac_1722_);
lean_dec(v_tac_1722_);
lean_dec(v___x_1736_);
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
return v___x_1738_;
}
else
{
lean_object* v_val_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1767_; 
v_val_1739_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1741_ = v___x_1731_;
v_isShared_1742_ = v_isSharedCheck_1767_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_val_1739_);
lean_dec(v___x_1731_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1767_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; uint8_t v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1743_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_1744_ = 0;
v___x_1745_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1730_, v___x_1743_, v_env_1729_, v_val_1739_, v___x_1744_);
lean_dec(v_val_1739_);
lean_dec_ref(v_env_1729_);
v___x_1746_ = lean_unsigned_to_nat(0u);
v___x_1747_ = lean_array_get_size(v___x_1745_);
v___x_1748_ = lean_nat_dec_lt(v___x_1746_, v___x_1747_);
if (v___x_1748_ == 0)
{
lean_dec_ref(v___x_1745_);
lean_del_object(v___x_1741_);
lean_dec(v_tac_1722_);
goto v___jp_1726_;
}
else
{
lean_object* v___x_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; 
v___x_1749_ = lean_unsigned_to_nat(1u);
v___x_1750_ = lean_nat_sub(v___x_1747_, v___x_1749_);
v___x_1751_ = lean_nat_dec_le(v___x_1746_, v___x_1750_);
if (v___x_1751_ == 0)
{
lean_dec(v___x_1750_);
lean_dec_ref(v___x_1745_);
lean_del_object(v___x_1741_);
lean_dec(v_tac_1722_);
goto v___jp_1726_;
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
v___x_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1753_, 0, v_tac_1722_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
v___x_1754_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v___x_1745_, v___x_1753_, v___x_1746_, v___x_1750_);
lean_dec_ref_known(v___x_1753_, 2);
lean_dec_ref(v___x_1745_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_del_object(v___x_1741_);
goto v___jp_1726_;
}
else
{
lean_object* v_val_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1766_; 
v_val_1755_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1757_ = v___x_1754_;
v_isShared_1758_ = v_isSharedCheck_1766_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_val_1755_);
lean_dec(v___x_1754_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1766_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v_snd_1759_; lean_object* v___x_1761_; 
v_snd_1759_ = lean_ctor_get(v_val_1755_, 1);
lean_inc(v_snd_1759_);
lean_dec(v_val_1755_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 0, v_snd_1759_);
v___x_1761_ = v___x_1757_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_snd_1759_);
v___x_1761_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1763_; 
if (v_isShared_1742_ == 0)
{
lean_ctor_set_tag(v___x_1741_, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1761_);
v___x_1763_ = v___x_1741_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
}
}
}
}
v___jp_1726_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = lean_box(0);
v___x_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1727_);
return v___x_1728_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object* v_tac_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_1768_, v___y_1769_);
lean_dec(v___y_1769_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object* v_t_1772_, lean_object* v_k_1773_){
_start:
{
if (lean_obj_tag(v_t_1772_) == 0)
{
lean_object* v_k_1774_; lean_object* v_v_1775_; lean_object* v_l_1776_; lean_object* v_r_1777_; uint8_t v___x_1778_; 
v_k_1774_ = lean_ctor_get(v_t_1772_, 1);
v_v_1775_ = lean_ctor_get(v_t_1772_, 2);
v_l_1776_ = lean_ctor_get(v_t_1772_, 3);
v_r_1777_ = lean_ctor_get(v_t_1772_, 4);
v___x_1778_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1773_, v_k_1774_);
switch(v___x_1778_)
{
case 0:
{
v_t_1772_ = v_l_1776_;
goto _start;
}
case 1:
{
lean_object* v___x_1780_; 
lean_inc(v_v_1775_);
v___x_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1780_, 0, v_v_1775_);
return v___x_1780_;
}
default: 
{
v_t_1772_ = v_r_1777_;
goto _start;
}
}
}
else
{
lean_object* v___x_1782_; 
v___x_1782_ = lean_box(0);
return v___x_1782_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg___boxed(lean_object* v_t_1783_, lean_object* v_k_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_1783_, v_k_1784_);
lean_dec(v_k_1784_);
lean_dec(v_t_1783_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(lean_object* v_a_1786_, lean_object* v_x_1787_){
_start:
{
if (lean_obj_tag(v_x_1787_) == 0)
{
lean_object* v___x_1788_; 
v___x_1788_ = lean_box(0);
return v___x_1788_;
}
else
{
lean_object* v_key_1789_; lean_object* v_value_1790_; lean_object* v_tail_1791_; uint8_t v___x_1792_; 
v_key_1789_ = lean_ctor_get(v_x_1787_, 0);
v_value_1790_ = lean_ctor_get(v_x_1787_, 1);
v_tail_1791_ = lean_ctor_get(v_x_1787_, 2);
v___x_1792_ = lean_name_eq(v_key_1789_, v_a_1786_);
if (v___x_1792_ == 0)
{
v_x_1787_ = v_tail_1791_;
goto _start;
}
else
{
lean_object* v___x_1794_; 
lean_inc(v_value_1790_);
v___x_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1794_, 0, v_value_1790_);
return v___x_1794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg___boxed(lean_object* v_a_1795_, lean_object* v_x_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_1795_, v_x_1796_);
lean_dec(v_x_1796_);
lean_dec(v_a_1795_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(lean_object* v_m_1798_, lean_object* v_a_1799_){
_start:
{
lean_object* v_buckets_1800_; lean_object* v___x_1801_; uint64_t v___y_1803_; 
v_buckets_1800_ = lean_ctor_get(v_m_1798_, 1);
v___x_1801_ = lean_array_get_size(v_buckets_1800_);
if (lean_obj_tag(v_a_1799_) == 0)
{
uint64_t v___x_1817_; 
v___x_1817_ = 1723ULL;
v___y_1803_ = v___x_1817_;
goto v___jp_1802_;
}
else
{
uint64_t v_hash_1818_; 
v_hash_1818_ = lean_ctor_get_uint64(v_a_1799_, sizeof(void*)*2);
v___y_1803_ = v_hash_1818_;
goto v___jp_1802_;
}
v___jp_1802_:
{
uint64_t v___x_1804_; uint64_t v___x_1805_; uint64_t v_fold_1806_; uint64_t v___x_1807_; uint64_t v___x_1808_; uint64_t v___x_1809_; size_t v___x_1810_; size_t v___x_1811_; size_t v___x_1812_; size_t v___x_1813_; size_t v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1804_ = 32ULL;
v___x_1805_ = lean_uint64_shift_right(v___y_1803_, v___x_1804_);
v_fold_1806_ = lean_uint64_xor(v___y_1803_, v___x_1805_);
v___x_1807_ = 16ULL;
v___x_1808_ = lean_uint64_shift_right(v_fold_1806_, v___x_1807_);
v___x_1809_ = lean_uint64_xor(v_fold_1806_, v___x_1808_);
v___x_1810_ = lean_uint64_to_usize(v___x_1809_);
v___x_1811_ = lean_usize_of_nat(v___x_1801_);
v___x_1812_ = ((size_t)1ULL);
v___x_1813_ = lean_usize_sub(v___x_1811_, v___x_1812_);
v___x_1814_ = lean_usize_land(v___x_1810_, v___x_1813_);
v___x_1815_ = lean_array_uget_borrowed(v_buckets_1800_, v___x_1814_);
v___x_1816_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_1799_, v___x_1815_);
return v___x_1816_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg___boxed(lean_object* v_m_1819_, lean_object* v_a_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_1819_, v_a_1820_);
lean_dec(v_a_1820_);
lean_dec_ref(v_m_1819_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_keys_1822_, lean_object* v_vals_1823_, lean_object* v_i_1824_, lean_object* v_k_1825_){
_start:
{
lean_object* v___x_1826_; uint8_t v___x_1827_; 
v___x_1826_ = lean_array_get_size(v_keys_1822_);
v___x_1827_ = lean_nat_dec_lt(v_i_1824_, v___x_1826_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; 
lean_dec(v_i_1824_);
v___x_1828_ = lean_box(0);
return v___x_1828_;
}
else
{
lean_object* v_k_x27_1829_; uint8_t v___x_1830_; 
v_k_x27_1829_ = lean_array_fget_borrowed(v_keys_1822_, v_i_1824_);
v___x_1830_ = lean_name_eq(v_k_1825_, v_k_x27_1829_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = lean_unsigned_to_nat(1u);
v___x_1832_ = lean_nat_add(v_i_1824_, v___x_1831_);
lean_dec(v_i_1824_);
v_i_1824_ = v___x_1832_;
goto _start;
}
else
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = lean_array_fget_borrowed(v_vals_1823_, v_i_1824_);
lean_dec(v_i_1824_);
lean_inc(v___x_1834_);
v___x_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
return v___x_1835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object* v_keys_1836_, lean_object* v_vals_1837_, lean_object* v_i_1838_, lean_object* v_k_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_1836_, v_vals_1837_, v_i_1838_, v_k_1839_);
lean_dec(v_k_1839_);
lean_dec_ref(v_vals_1837_);
lean_dec_ref(v_keys_1836_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object* v_x_1841_, size_t v_x_1842_, lean_object* v_x_1843_){
_start:
{
if (lean_obj_tag(v_x_1841_) == 0)
{
lean_object* v_es_1844_; lean_object* v___x_1845_; size_t v___x_1846_; size_t v___x_1847_; lean_object* v_j_1848_; lean_object* v___x_1849_; 
v_es_1844_ = lean_ctor_get(v_x_1841_, 0);
v___x_1845_ = lean_box(2);
v___x_1846_ = ((size_t)31ULL);
v___x_1847_ = lean_usize_land(v_x_1842_, v___x_1846_);
v_j_1848_ = lean_usize_to_nat(v___x_1847_);
v___x_1849_ = lean_array_get_borrowed(v___x_1845_, v_es_1844_, v_j_1848_);
lean_dec(v_j_1848_);
switch(lean_obj_tag(v___x_1849_))
{
case 0:
{
lean_object* v_key_1850_; lean_object* v_val_1851_; uint8_t v___x_1852_; 
v_key_1850_ = lean_ctor_get(v___x_1849_, 0);
v_val_1851_ = lean_ctor_get(v___x_1849_, 1);
v___x_1852_ = lean_name_eq(v_x_1843_, v_key_1850_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; 
v___x_1853_ = lean_box(0);
return v___x_1853_;
}
else
{
lean_object* v___x_1854_; 
lean_inc(v_val_1851_);
v___x_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1854_, 0, v_val_1851_);
return v___x_1854_;
}
}
case 1:
{
lean_object* v_node_1855_; size_t v___x_1856_; size_t v___x_1857_; 
v_node_1855_ = lean_ctor_get(v___x_1849_, 0);
v___x_1856_ = ((size_t)5ULL);
v___x_1857_ = lean_usize_shift_right(v_x_1842_, v___x_1856_);
v_x_1841_ = v_node_1855_;
v_x_1842_ = v___x_1857_;
goto _start;
}
default: 
{
lean_object* v___x_1859_; 
v___x_1859_ = lean_box(0);
return v___x_1859_;
}
}
}
else
{
lean_object* v_ks_1860_; lean_object* v_vs_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v_ks_1860_ = lean_ctor_get(v_x_1841_, 0);
v_vs_1861_ = lean_ctor_get(v_x_1841_, 1);
v___x_1862_ = lean_unsigned_to_nat(0u);
v___x_1863_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_ks_1860_, v_vs_1861_, v___x_1862_, v_x_1843_);
return v___x_1863_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_1864_, lean_object* v_x_1865_, lean_object* v_x_1866_){
_start:
{
size_t v_x_17280__boxed_1867_; lean_object* v_res_1868_; 
v_x_17280__boxed_1867_ = lean_unbox_usize(v_x_1865_);
lean_dec(v_x_1865_);
v_res_1868_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1864_, v_x_17280__boxed_1867_, v_x_1866_);
lean_dec(v_x_1866_);
lean_dec_ref(v_x_1864_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object* v_x_1869_, lean_object* v_x_1870_){
_start:
{
uint64_t v___y_1872_; 
if (lean_obj_tag(v_x_1870_) == 0)
{
uint64_t v___x_1875_; 
v___x_1875_ = 1723ULL;
v___y_1872_ = v___x_1875_;
goto v___jp_1871_;
}
else
{
uint64_t v_hash_1876_; 
v_hash_1876_ = lean_ctor_get_uint64(v_x_1870_, sizeof(void*)*2);
v___y_1872_ = v_hash_1876_;
goto v___jp_1871_;
}
v___jp_1871_:
{
size_t v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = lean_uint64_to_usize(v___y_1872_);
v___x_1874_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1869_, v___x_1873_, v_x_1870_);
return v___x_1874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object* v_x_1877_, lean_object* v_x_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_1877_, v_x_1878_);
lean_dec(v_x_1878_);
lean_dec_ref(v_x_1877_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object* v_x_1880_, lean_object* v_x_1881_){
_start:
{
uint8_t v_stage_u2081_1882_; 
v_stage_u2081_1882_ = lean_ctor_get_uint8(v_x_1880_, sizeof(void*)*2);
if (v_stage_u2081_1882_ == 0)
{
lean_object* v_map_u2081_1883_; lean_object* v_map_u2082_1884_; lean_object* v___x_1885_; 
v_map_u2081_1883_ = lean_ctor_get(v_x_1880_, 0);
v_map_u2082_1884_ = lean_ctor_get(v_x_1880_, 1);
v___x_1885_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_1883_, v_x_1881_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_map_u2082_1884_, v_x_1881_);
return v___x_1886_;
}
else
{
return v___x_1885_;
}
}
else
{
lean_object* v_map_u2081_1887_; lean_object* v___x_1888_; 
v_map_u2081_1887_ = lean_ctor_get(v_x_1880_, 0);
v___x_1888_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_1887_, v_x_1881_);
return v___x_1888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg___boxed(lean_object* v_x_1889_, lean_object* v_x_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_1889_, v_x_1890_);
lean_dec(v_x_1890_);
lean_dec_ref(v_x_1889_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object* v_firsts_1892_, lean_object* v_n_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1912_; lean_object* v_val_1913_; lean_object* v___x_1915_; lean_object* v___y_1917_; lean_object* v_env_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1915_ = lean_st_ref_get(v___y_1895_);
v_env_1932_ = lean_ctor_get(v___x_1915_, 0);
lean_inc_ref(v_env_1932_);
lean_dec(v___x_1915_);
v___x_1933_ = l_Lean_Environment_constants(v_env_1932_);
v___x_1934_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v___x_1933_, v_n_1893_);
lean_dec_ref(v___x_1933_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v___x_1935_; 
v___x_1935_ = lean_box(0);
v___y_1917_ = v___x_1935_;
goto v___jp_1916_;
}
else
{
lean_object* v_val_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v_val_1936_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_val_1936_);
lean_dec_ref_known(v___x_1934_, 1);
v___x_1937_ = l_Lean_ConstantInfo_levelParams(v_val_1936_);
lean_dec(v_val_1936_);
v___x_1938_ = lean_box(0);
v___x_1939_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(v___x_1937_, v___x_1938_);
v___y_1917_ = v___x_1939_;
goto v___jp_1916_;
}
v___jp_1897_:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; uint8_t v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1900_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8);
v___x_1901_ = l_Lean_Expr_const___override(v_n_1893_, v___y_1898_);
v___x_1902_ = lean_unsigned_to_nat(32u);
v___x_1903_ = lean_mk_empty_array_with_capacity(v___x_1902_);
lean_dec_ref(v___x_1903_);
v___x_1904_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2);
v___x_1905_ = lean_box(0);
v___x_1906_ = 0;
v___x_1907_ = l_Lean_MessageData_withExprHover(v___y_1899_, v___x_1901_, v___x_1904_, v___x_1905_, v___x_1905_, v___x_1905_, v___x_1906_);
v___x_1908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1900_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
lean_ctor_set(v___x_1909_, 1, v___x_1900_);
v___x_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
return v___x_1910_;
}
v___jp_1911_:
{
lean_object* v___x_1914_; 
v___x_1914_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1914_, 0, v_val_1913_);
v___y_1898_ = v___y_1912_;
v___y_1899_ = v___x_1914_;
goto v___jp_1897_;
}
v___jp_1916_:
{
lean_object* v___x_1918_; lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1931_; 
lean_inc(v_n_1893_);
v___x_1918_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_n_1893_, v___y_1895_);
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1931_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1931_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
if (lean_obj_tag(v_a_1919_) == 0)
{
lean_object* v___x_1923_; 
v___x_1923_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_firsts_1892_, v_n_1893_);
if (lean_obj_tag(v___x_1923_) == 0)
{
uint8_t v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1924_ = 1;
lean_inc(v_n_1893_);
v___x_1925_ = l_Lean_Name_toString(v_n_1893_, v___x_1924_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set_tag(v___x_1921_, 3);
lean_ctor_set(v___x_1921_, 0, v___x_1925_);
v___x_1927_ = v___x_1921_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
v___y_1898_ = v___y_1917_;
v___y_1899_ = v___x_1927_;
goto v___jp_1897_;
}
}
else
{
lean_object* v_val_1929_; 
lean_del_object(v___x_1921_);
v_val_1929_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_val_1929_);
lean_dec_ref_known(v___x_1923_, 1);
v___y_1912_ = v___y_1917_;
v_val_1913_ = v_val_1929_;
goto v___jp_1911_;
}
}
else
{
lean_object* v_val_1930_; 
lean_del_object(v___x_1921_);
v_val_1930_ = lean_ctor_get(v_a_1919_, 0);
lean_inc(v_val_1930_);
lean_dec_ref_known(v_a_1919_, 1);
v___y_1912_ = v___y_1917_;
v_val_1913_ = v_val_1930_;
goto v___jp_1911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object* v_firsts_1940_, lean_object* v_n_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_firsts_1940_, v_n_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v_firsts_1940_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object* v_a_1946_, lean_object* v_x_1947_, lean_object* v_x_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
if (lean_obj_tag(v_x_1947_) == 0)
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1952_ = l_List_reverse___redArg(v_x_1948_);
v___x_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
return v___x_1953_;
}
else
{
lean_object* v_head_1954_; lean_object* v_tail_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1973_; 
v_head_1954_ = lean_ctor_get(v_x_1947_, 0);
v_tail_1955_ = lean_ctor_get(v_x_1947_, 1);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_x_1947_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1957_ = v_x_1947_;
v_isShared_1958_ = v_isSharedCheck_1973_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_tail_1955_);
lean_inc(v_head_1954_);
lean_dec(v_x_1947_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1973_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; 
v___x_1959_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_a_1946_, v_head_1954_, v___y_1949_, v___y_1950_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v___x_1962_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1960_);
lean_dec_ref_known(v___x_1959_, 1);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 1, v_x_1948_);
lean_ctor_set(v___x_1957_, 0, v_a_1960_);
v___x_1962_ = v___x_1957_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1960_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_x_1948_);
v___x_1962_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
v_x_1947_ = v_tail_1955_;
v_x_1948_ = v___x_1962_;
goto _start;
}
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_del_object(v___x_1957_);
lean_dec(v_tail_1955_);
lean_dec(v_x_1948_);
v_a_1965_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1959_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1959_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object* v_a_1974_, lean_object* v_x_1975_, lean_object* v_x_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_1974_, v_x_1975_, v_x_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v_a_1974_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object* v_val_1981_, lean_object* v___x_1982_, lean_object* v___x_1983_, lean_object* v_a_1984_, lean_object* v_b_1985_){
_start:
{
lean_object* v_it_1987_; lean_object* v_startInclusive_1988_; lean_object* v_endExclusive_1989_; 
if (lean_obj_tag(v_a_1984_) == 0)
{
lean_object* v_currPos_1994_; lean_object* v_searcher_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2018_; 
v_currPos_1994_ = lean_ctor_get(v_a_1984_, 0);
v_searcher_1995_ = lean_ctor_get(v_a_1984_, 1);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_a_1984_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_1997_ = v_a_1984_;
v_isShared_1998_ = v_isSharedCheck_2018_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_searcher_1995_);
lean_inc(v_currPos_1994_);
lean_dec(v_a_1984_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2018_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
uint8_t v_decide_1999_; 
v_decide_1999_ = lean_nat_dec_eq(v_searcher_1995_, v___x_1983_);
if (v_decide_1999_ == 0)
{
uint32_t v___x_2000_; uint32_t v___x_2001_; uint8_t v___x_2002_; 
v___x_2000_ = 10;
v___x_2001_ = lean_string_utf8_get_fast(v_val_1981_, v_searcher_1995_);
v___x_2002_ = lean_uint32_dec_eq(v___x_2001_, v___x_2000_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2003_ = lean_string_utf8_next_fast(v_val_1981_, v_searcher_1995_);
lean_dec(v_searcher_1995_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 1, v___x_2003_);
v___x_2005_ = v___x_1997_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_currPos_1994_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v___x_2003_);
v___x_2005_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
v_a_1984_ = v___x_2005_;
goto _start;
}
}
else
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v_slice_2011_; lean_object* v_nextIt_2013_; 
v___x_2008_ = lean_string_utf8_next_fast(v_val_1981_, v_searcher_1995_);
v___x_2009_ = lean_nat_sub(v___x_2008_, v_searcher_1995_);
v___x_2010_ = lean_nat_add(v_searcher_1995_, v___x_2009_);
lean_dec(v___x_2009_);
v_slice_2011_ = l_String_Slice_subslice_x21(v___x_1982_, v_currPos_1994_, v_searcher_1995_);
lean_inc(v___x_2010_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 1, v___x_2010_);
lean_ctor_set(v___x_1997_, 0, v___x_2010_);
v_nextIt_2013_ = v___x_1997_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v___x_2010_);
v_nextIt_2013_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v_startInclusive_2014_; lean_object* v_endExclusive_2015_; 
v_startInclusive_2014_ = lean_ctor_get(v_slice_2011_, 0);
lean_inc(v_startInclusive_2014_);
v_endExclusive_2015_ = lean_ctor_get(v_slice_2011_, 1);
lean_inc(v_endExclusive_2015_);
lean_dec_ref(v_slice_2011_);
v_it_1987_ = v_nextIt_2013_;
v_startInclusive_1988_ = v_startInclusive_2014_;
v_endExclusive_1989_ = v_endExclusive_2015_;
goto v___jp_1986_;
}
}
}
else
{
lean_object* v___x_2017_; 
lean_del_object(v___x_1997_);
lean_dec(v_searcher_1995_);
v___x_2017_ = lean_box(1);
lean_inc(v___x_1983_);
v_it_1987_ = v___x_2017_;
v_startInclusive_1988_ = v_currPos_1994_;
v_endExclusive_1989_ = v___x_1983_;
goto v___jp_1986_;
}
}
}
else
{
lean_dec(v___x_1983_);
return v_b_1985_;
}
v___jp_1986_:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1990_ = lean_string_utf8_extract_fast(v_val_1981_, v_startInclusive_1988_, v_endExclusive_1989_);
lean_dec(v_endExclusive_1989_);
lean_dec(v_startInclusive_1988_);
v___x_1991_ = l_Lean_stringToMessageData(v___x_1990_);
v___x_1992_ = lean_array_push(v_b_1985_, v___x_1991_);
v_a_1984_ = v_it_1987_;
v_b_1985_ = v___x_1992_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object* v_val_2019_, lean_object* v___x_2020_, lean_object* v___x_2021_, lean_object* v_a_2022_, lean_object* v_b_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2019_, v___x_2020_, v___x_2021_, v_a_2022_, v_b_2023_);
lean_dec_ref(v___x_2020_);
lean_dec_ref(v_val_2019_);
return v_res_2024_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2(void){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1));
v___x_2029_ = l_Lean_stringToMessageData(v___x_2028_);
return v___x_2029_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4(void){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3));
v___x_2032_ = l_Lean_stringToMessageData(v___x_2031_);
return v___x_2032_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6(void){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5));
v___x_2035_ = l_Lean_stringToMessageData(v___x_2034_);
return v___x_2035_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9(void){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2039_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8));
v___x_2040_ = l_Lean_MessageData_ofFormat(v___x_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_x_2043_, lean_object* v_x_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
if (lean_obj_tag(v_x_2043_) == 0)
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = l_List_reverse___redArg(v_x_2044_);
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
return v___x_2049_;
}
else
{
lean_object* v_head_2050_; lean_object* v_tail_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2148_; 
v_head_2050_ = lean_ctor_get(v_x_2043_, 0);
v_tail_2051_ = lean_ctor_get(v_x_2043_, 1);
v_isSharedCheck_2148_ = !lean_is_exclusive(v_x_2043_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2053_ = v_x_2043_;
v_isShared_2054_ = v_isSharedCheck_2148_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_tail_2051_);
lean_inc(v_head_2050_);
lean_dec(v_x_2043_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2148_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v_snd_2068_; lean_object* v_fst_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2147_; 
v_snd_2068_ = lean_ctor_get(v_head_2050_, 1);
v_fst_2069_ = lean_ctor_get(v_head_2050_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_head_2050_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2071_ = v_head_2050_;
v_isShared_2072_ = v_isSharedCheck_2147_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_snd_2068_);
lean_inc(v_fst_2069_);
lean_dec(v_head_2050_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2147_;
goto v_resetjp_2070_;
}
v___jp_2055_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___y_2058_);
lean_ctor_set(v___x_2060_, 1, v___y_2059_);
v___x_2061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
lean_ctor_set(v___x_2061_, 1, v___y_2057_);
v___x_2062_ = l_Lean_MessageData_nestD(v___x_2061_);
lean_inc_ref(v___y_2056_);
v___x_2063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___y_2056_);
lean_ctor_set(v___x_2063_, 1, v___x_2062_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 1, v_x_2044_);
lean_ctor_set(v___x_2053_, 0, v___x_2063_);
v___x_2065_ = v___x_2053_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_x_2044_);
v___x_2065_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
v_x_2043_ = v_tail_2051_;
v_x_2044_ = v___x_2065_;
goto _start;
}
}
v_resetjp_2070_:
{
lean_object* v_fst_2073_; lean_object* v_snd_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2146_; 
v_fst_2073_ = lean_ctor_get(v_snd_2068_, 0);
v_snd_2074_ = lean_ctor_get(v_snd_2068_, 1);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_snd_2068_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2076_ = v_snd_2068_;
v_isShared_2077_ = v_isSharedCheck_2146_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_snd_2074_);
lean_inc(v_fst_2073_);
lean_dec(v_snd_2068_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2146_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v_a_2101_; lean_object* v___y_2117_; lean_object* v___x_2126_; 
v___x_2126_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2042_, v_fst_2069_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v___x_2127_; 
v___x_2127_ = l_Lean_MessageData_nil;
v_a_2101_ = v___x_2127_;
goto v___jp_2100_;
}
else
{
lean_object* v_val_2128_; 
v_val_2128_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_val_2128_);
lean_dec_ref_known(v___x_2126_, 1);
if (lean_obj_tag(v_val_2128_) == 0)
{
lean_object* v_size_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___x_2137_; uint8_t v___x_2138_; 
v_size_2129_ = lean_ctor_get(v_val_2128_, 0);
v___x_2130_ = lean_mk_empty_array_with_capacity(v_size_2129_);
v___x_2131_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v___x_2130_, v_val_2128_);
v___x_2132_ = lean_array_get_size(v___x_2131_);
v___x_2137_ = lean_unsigned_to_nat(0u);
v___x_2138_ = lean_nat_dec_eq(v___x_2132_, v___x_2137_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___y_2142_; uint8_t v___x_2144_; 
v___x_2139_ = lean_unsigned_to_nat(1u);
v___x_2140_ = lean_nat_sub(v___x_2132_, v___x_2139_);
v___x_2144_ = lean_nat_dec_le(v___x_2137_, v___x_2140_);
if (v___x_2144_ == 0)
{
lean_inc(v___x_2140_);
v___y_2142_ = v___x_2140_;
goto v___jp_2141_;
}
else
{
v___y_2142_ = v___x_2137_;
goto v___jp_2141_;
}
v___jp_2141_:
{
uint8_t v___x_2143_; 
v___x_2143_ = lean_nat_dec_le(v___y_2142_, v___x_2140_);
if (v___x_2143_ == 0)
{
lean_dec(v___x_2140_);
lean_inc(v___y_2142_);
v___y_2134_ = v___y_2142_;
v___y_2135_ = v___y_2142_;
goto v___jp_2133_;
}
else
{
v___y_2134_ = v___y_2142_;
v___y_2135_ = v___x_2140_;
goto v___jp_2133_;
}
}
}
else
{
v___y_2117_ = v___x_2131_;
goto v___jp_2116_;
}
v___jp_2133_:
{
lean_object* v___x_2136_; 
v___x_2136_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v___x_2132_, v___x_2131_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
v___y_2117_ = v___x_2136_;
goto v___jp_2116_;
}
}
else
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Lean_MessageData_nil;
v_a_2101_ = v___x_2145_;
goto v___jp_2100_;
}
}
v___jp_2078_:
{
lean_object* v___x_2084_; 
if (v_isShared_2077_ == 0)
{
lean_ctor_set_tag(v___x_2076_, 7);
lean_ctor_set(v___x_2076_, 1, v___y_2082_);
lean_ctor_set(v___x_2076_, 0, v___y_2081_);
v___x_2084_ = v___x_2076_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___y_2081_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v___y_2082_);
v___x_2084_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
if (lean_obj_tag(v_snd_2074_) == 0)
{
lean_object* v___x_2085_; 
lean_del_object(v___x_2071_);
v___x_2085_ = l_Lean_MessageData_nil;
v___y_2056_ = v___y_2080_;
v___y_2057_ = v___y_2079_;
v___y_2058_ = v___x_2084_;
v___y_2059_ = v___x_2085_;
goto v___jp_2055_;
}
else
{
lean_object* v_val_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2097_; 
v_val_2086_ = lean_ctor_get(v_snd_2074_, 0);
lean_inc_n(v_val_2086_, 2);
lean_dec_ref_known(v_snd_2074_, 1);
v___x_2087_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2088_ = lean_unsigned_to_nat(0u);
v___x_2089_ = lean_string_utf8_byte_size(v_val_2086_);
v___x_2090_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2090_, 0, v_val_2086_);
lean_ctor_set(v___x_2090_, 1, v___x_2088_);
lean_ctor_set(v___x_2090_, 2, v___x_2089_);
v___x_2091_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v___x_2090_);
v___x_2092_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0));
v___x_2093_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2086_, v___x_2090_, v___x_2089_, v___x_2091_, v___x_2092_);
lean_dec_ref_known(v___x_2090_, 3);
lean_dec(v_val_2086_);
v___x_2094_ = lean_array_to_list(v___x_2093_);
v___x_2095_ = l_Lean_MessageData_joinSep(v___x_2094_, v___x_2087_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set_tag(v___x_2071_, 7);
lean_ctor_set(v___x_2071_, 1, v___x_2095_);
lean_ctor_set(v___x_2071_, 0, v___x_2087_);
v___x_2097_ = v___x_2071_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2087_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
v___y_2056_ = v___y_2080_;
v___y_2057_ = v___y_2079_;
v___y_2058_ = v___x_2084_;
v___y_2059_ = v___x_2097_;
goto v___jp_2055_;
}
}
}
}
v___jp_2100_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; lean_object* v___x_2108_; uint8_t v___x_2109_; 
v___x_2102_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2);
v___x_2103_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8);
lean_inc(v_fst_2069_);
v___x_2104_ = l_Lean_MessageData_ofName(v_fst_2069_);
v___x_2105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2103_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
v___x_2106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
lean_ctor_set(v___x_2106_, 1, v___x_2103_);
v___x_2107_ = 1;
v___x_2108_ = l_Lean_Name_toString(v_fst_2069_, v___x_2107_);
v___x_2109_ = lean_string_dec_eq(v___x_2108_, v_fst_2073_);
lean_dec_ref(v___x_2108_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2110_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4);
v___x_2111_ = l_Lean_stringToMessageData(v_fst_2073_);
v___x_2112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2110_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6);
v___x_2114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2112_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
v___y_2079_ = v_a_2101_;
v___y_2080_ = v___x_2102_;
v___y_2081_ = v___x_2106_;
v___y_2082_ = v___x_2114_;
goto v___jp_2078_;
}
else
{
lean_object* v___x_2115_; 
lean_dec(v_fst_2073_);
v___x_2115_ = l_Lean_MessageData_nil;
v___y_2079_ = v_a_2101_;
v___y_2080_ = v___x_2102_;
v___y_2081_ = v___x_2106_;
v___y_2082_ = v___x_2115_;
goto v___jp_2078_;
}
}
v___jp_2116_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2118_ = lean_array_to_list(v___y_2117_);
v___x_2119_ = lean_box(0);
v___x_2120_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_2041_, v___x_2118_, v___x_2119_, v___y_2045_, v___y_2046_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v___x_2120_, 1);
v___x_2122_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2123_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9);
v___x_2124_ = l_Lean_MessageData_joinSep(v_a_2121_, v___x_2123_);
v___x_2125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2122_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v_a_2101_ = v___x_2125_;
goto v___jp_2100_;
}
else
{
lean_del_object(v___x_2076_);
lean_dec(v_snd_2074_);
lean_dec(v_fst_2073_);
lean_del_object(v___x_2071_);
lean_dec(v_fst_2069_);
lean_del_object(v___x_2053_);
lean_dec(v_tail_2051_);
lean_dec(v_x_2044_);
return v___x_2120_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_x_2151_, lean_object* v_x_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_2149_, v_a_2150_, v_x_2151_, v_x_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v_a_2150_);
lean_dec(v_a_2149_);
return v_res_2156_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(uint8_t v_suppressElabErrors_2158_, uint8_t v___y_2159_, lean_object* v_x_2160_){
_start:
{
if (lean_obj_tag(v_x_2160_) == 1)
{
lean_object* v_pre_2161_; 
v_pre_2161_ = lean_ctor_get(v_x_2160_, 0);
if (lean_obj_tag(v_pre_2161_) == 0)
{
lean_object* v_str_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; 
v_str_2162_ = lean_ctor_get(v_x_2160_, 1);
v___x_2163_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0));
v___x_2164_ = lean_string_dec_eq(v_str_2162_, v___x_2163_);
if (v___x_2164_ == 0)
{
return v___x_2164_;
}
else
{
return v_suppressElabErrors_2158_;
}
}
else
{
return v___y_2159_;
}
}
else
{
return v___y_2159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed(lean_object* v_suppressElabErrors_2165_, lean_object* v___y_2166_, lean_object* v_x_2167_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2168_; uint8_t v___y_17895__boxed_2169_; uint8_t v_res_2170_; lean_object* v_r_2171_; 
v_suppressElabErrors_boxed_2168_ = lean_unbox(v_suppressElabErrors_2165_);
v___y_17895__boxed_2169_ = lean_unbox(v___y_2166_);
v_res_2170_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(v_suppressElabErrors_boxed_2168_, v___y_17895__boxed_2169_, v_x_2167_);
lean_dec(v_x_2167_);
v_r_2171_ = lean_box(v_res_2170_);
return v_r_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(lean_object* v_ref_2172_, lean_object* v_msgData_2173_, uint8_t v_severity_2174_, uint8_t v_isSilent_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; uint8_t v___y_2183_; lean_object* v___y_2184_; uint8_t v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; uint8_t v___y_2245_; uint8_t v___y_2246_; uint8_t v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; uint8_t v___y_2273_; uint8_t v___y_2274_; lean_object* v___y_2275_; uint8_t v___y_2276_; lean_object* v___y_2277_; uint8_t v___y_2281_; uint8_t v___y_2282_; uint8_t v___y_2283_; uint8_t v___x_2298_; uint8_t v___y_2300_; uint8_t v___y_2301_; uint8_t v___y_2302_; uint8_t v___y_2304_; uint8_t v___x_2316_; 
v___x_2298_ = 2;
v___x_2316_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2174_, v___x_2298_);
if (v___x_2316_ == 0)
{
v___y_2304_ = v___x_2316_;
goto v___jp_2303_;
}
else
{
uint8_t v___x_2317_; 
lean_inc_ref(v_msgData_2173_);
v___x_2317_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2173_);
v___y_2304_ = v___x_2317_;
goto v___jp_2303_;
}
v___jp_2179_:
{
lean_object* v___x_2188_; 
v___x_2188_ = l_Lean_Elab_Command_getScope___redArg(v___y_2187_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2190_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2189_);
lean_dec_ref_known(v___x_2188_, 1);
v___x_2190_ = l_Lean_Elab_Command_getScope___redArg(v___y_2187_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2227_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2193_ = v___x_2190_;
v_isShared_2194_ = v_isSharedCheck_2227_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2227_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; lean_object* v_currNamespace_2196_; lean_object* v_openDecls_2197_; lean_object* v_env_2198_; lean_object* v_messages_2199_; lean_object* v_scopes_2200_; lean_object* v_usedQuotCtxts_2201_; lean_object* v_nextMacroScope_2202_; lean_object* v_maxRecDepth_2203_; lean_object* v_ngen_2204_; lean_object* v_auxDeclNGen_2205_; lean_object* v_infoState_2206_; lean_object* v_traceState_2207_; lean_object* v_snapshotTasks_2208_; lean_object* v_prevLinterStates_2209_; lean_object* v_codeQualityEntryTasks_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2226_; 
v___x_2195_ = lean_st_ref_take(v___y_2187_);
v_currNamespace_2196_ = lean_ctor_get(v_a_2189_, 2);
lean_inc(v_currNamespace_2196_);
lean_dec(v_a_2189_);
v_openDecls_2197_ = lean_ctor_get(v_a_2191_, 3);
lean_inc(v_openDecls_2197_);
lean_dec(v_a_2191_);
v_env_2198_ = lean_ctor_get(v___x_2195_, 0);
v_messages_2199_ = lean_ctor_get(v___x_2195_, 1);
v_scopes_2200_ = lean_ctor_get(v___x_2195_, 2);
v_usedQuotCtxts_2201_ = lean_ctor_get(v___x_2195_, 3);
v_nextMacroScope_2202_ = lean_ctor_get(v___x_2195_, 4);
v_maxRecDepth_2203_ = lean_ctor_get(v___x_2195_, 5);
v_ngen_2204_ = lean_ctor_get(v___x_2195_, 6);
v_auxDeclNGen_2205_ = lean_ctor_get(v___x_2195_, 7);
v_infoState_2206_ = lean_ctor_get(v___x_2195_, 8);
v_traceState_2207_ = lean_ctor_get(v___x_2195_, 9);
v_snapshotTasks_2208_ = lean_ctor_get(v___x_2195_, 10);
v_prevLinterStates_2209_ = lean_ctor_get(v___x_2195_, 11);
v_codeQualityEntryTasks_2210_ = lean_ctor_get(v___x_2195_, 12);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2212_ = v___x_2195_;
v_isShared_2213_ = v_isSharedCheck_2226_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2210_);
lean_inc(v_prevLinterStates_2209_);
lean_inc(v_snapshotTasks_2208_);
lean_inc(v_traceState_2207_);
lean_inc(v_infoState_2206_);
lean_inc(v_auxDeclNGen_2205_);
lean_inc(v_ngen_2204_);
lean_inc(v_maxRecDepth_2203_);
lean_inc(v_nextMacroScope_2202_);
lean_inc(v_usedQuotCtxts_2201_);
lean_inc(v_scopes_2200_);
lean_inc(v_messages_2199_);
lean_inc(v_env_2198_);
lean_dec(v___x_2195_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2226_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2219_; 
v___x_2214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2214_, 0, v_currNamespace_2196_);
lean_ctor_set(v___x_2214_, 1, v_openDecls_2197_);
v___x_2215_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
lean_ctor_set(v___x_2215_, 1, v___y_2181_);
lean_inc_ref(v___y_2182_);
lean_inc_ref(v___y_2186_);
v___x_2216_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2216_, 0, v___y_2186_);
lean_ctor_set(v___x_2216_, 1, v___y_2184_);
lean_ctor_set(v___x_2216_, 2, v___y_2180_);
lean_ctor_set(v___x_2216_, 3, v___y_2182_);
lean_ctor_set(v___x_2216_, 4, v___x_2215_);
lean_ctor_set_uint8(v___x_2216_, sizeof(void*)*5, v___y_2185_);
lean_ctor_set_uint8(v___x_2216_, sizeof(void*)*5 + 1, v___y_2183_);
lean_ctor_set_uint8(v___x_2216_, sizeof(void*)*5 + 2, v_isSilent_2175_);
v___x_2217_ = l_Lean_MessageLog_add(v___x_2216_, v_messages_2199_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 1, v___x_2217_);
v___x_2219_ = v___x_2212_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_env_2198_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v___x_2217_);
lean_ctor_set(v_reuseFailAlloc_2225_, 2, v_scopes_2200_);
lean_ctor_set(v_reuseFailAlloc_2225_, 3, v_usedQuotCtxts_2201_);
lean_ctor_set(v_reuseFailAlloc_2225_, 4, v_nextMacroScope_2202_);
lean_ctor_set(v_reuseFailAlloc_2225_, 5, v_maxRecDepth_2203_);
lean_ctor_set(v_reuseFailAlloc_2225_, 6, v_ngen_2204_);
lean_ctor_set(v_reuseFailAlloc_2225_, 7, v_auxDeclNGen_2205_);
lean_ctor_set(v_reuseFailAlloc_2225_, 8, v_infoState_2206_);
lean_ctor_set(v_reuseFailAlloc_2225_, 9, v_traceState_2207_);
lean_ctor_set(v_reuseFailAlloc_2225_, 10, v_snapshotTasks_2208_);
lean_ctor_set(v_reuseFailAlloc_2225_, 11, v_prevLinterStates_2209_);
lean_ctor_set(v_reuseFailAlloc_2225_, 12, v_codeQualityEntryTasks_2210_);
v___x_2219_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2223_; 
v___x_2220_ = lean_st_ref_put(v___y_2187_, v___x_2219_);
v___x_2221_ = lean_box(0);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v___x_2221_);
v___x_2223_ = v___x_2193_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2221_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec(v_a_2189_);
lean_dec_ref(v___y_2184_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
v_a_2228_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2190_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2190_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_dec_ref(v___y_2184_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
v_a_2236_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2188_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2188_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
v___jp_2244_:
{
lean_object* v_fileName_2250_; lean_object* v_fileMap_2251_; uint8_t v_suppressElabErrors_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2271_; 
v_fileName_2250_ = lean_ctor_get(v___y_2176_, 0);
v_fileMap_2251_ = lean_ctor_get(v___y_2176_, 1);
v_suppressElabErrors_2252_ = lean_ctor_get_uint8(v___y_2176_, sizeof(void*)*10);
v___x_2253_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2173_);
v___x_2254_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v___x_2253_, v___y_2177_);
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2257_ = v___x_2254_;
v_isShared_2258_ = v_isSharedCheck_2271_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2254_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2271_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
lean_inc_ref_n(v_fileMap_2251_, 2);
v___x_2259_ = l_Lean_FileMap_toPosition(v_fileMap_2251_, v___y_2248_);
lean_dec(v___y_2248_);
v___x_2260_ = l_Lean_FileMap_toPosition(v_fileMap_2251_, v___y_2249_);
lean_dec(v___y_2249_);
v___x_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
v___x_2262_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
if (v_suppressElabErrors_2252_ == 0)
{
lean_del_object(v___x_2257_);
v___y_2180_ = v___x_2261_;
v___y_2181_ = v_a_2255_;
v___y_2182_ = v___x_2262_;
v___y_2183_ = v___y_2246_;
v___y_2184_ = v___x_2259_;
v___y_2185_ = v___y_2247_;
v___y_2186_ = v_fileName_2250_;
v___y_2187_ = v___y_2177_;
goto v___jp_2179_;
}
else
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___f_2265_; uint8_t v___x_2266_; 
v___x_2263_ = lean_box(v_suppressElabErrors_2252_);
v___x_2264_ = lean_box(v___y_2245_);
v___f_2265_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2265_, 0, v___x_2263_);
lean_closure_set(v___f_2265_, 1, v___x_2264_);
lean_inc(v_a_2255_);
v___x_2266_ = l_Lean_MessageData_hasTag(v___f_2265_, v_a_2255_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2267_; lean_object* v___x_2269_; 
lean_dec_ref_known(v___x_2261_, 1);
lean_dec_ref(v___x_2259_);
lean_dec(v_a_2255_);
v___x_2267_ = lean_box(0);
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 0, v___x_2267_);
v___x_2269_ = v___x_2257_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
else
{
lean_del_object(v___x_2257_);
v___y_2180_ = v___x_2261_;
v___y_2181_ = v_a_2255_;
v___y_2182_ = v___x_2262_;
v___y_2183_ = v___y_2246_;
v___y_2184_ = v___x_2259_;
v___y_2185_ = v___y_2247_;
v___y_2186_ = v_fileName_2250_;
v___y_2187_ = v___y_2177_;
goto v___jp_2179_;
}
}
}
}
v___jp_2272_:
{
lean_object* v___x_2278_; 
v___x_2278_ = l_Lean_Syntax_getTailPos_x3f(v___y_2275_, v___y_2276_);
lean_dec(v___y_2275_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_inc(v___y_2277_);
v___y_2245_ = v___y_2273_;
v___y_2246_ = v___y_2274_;
v___y_2247_ = v___y_2276_;
v___y_2248_ = v___y_2277_;
v___y_2249_ = v___y_2277_;
goto v___jp_2244_;
}
else
{
lean_object* v_val_2279_; 
v_val_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_val_2279_);
lean_dec_ref_known(v___x_2278_, 1);
v___y_2245_ = v___y_2273_;
v___y_2246_ = v___y_2274_;
v___y_2247_ = v___y_2276_;
v___y_2248_ = v___y_2277_;
v___y_2249_ = v_val_2279_;
goto v___jp_2244_;
}
}
v___jp_2280_:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Lean_Elab_Command_getRef___redArg(v___y_2176_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v_ref_2286_; lean_object* v___x_2287_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref_known(v___x_2284_, 1);
v_ref_2286_ = l_Lean_replaceRef(v_ref_2172_, v_a_2285_);
lean_dec(v_a_2285_);
v___x_2287_ = l_Lean_Syntax_getPos_x3f(v_ref_2286_, v___y_2282_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v___x_2288_; 
v___x_2288_ = lean_unsigned_to_nat(0u);
v___y_2273_ = v___y_2281_;
v___y_2274_ = v___y_2283_;
v___y_2275_ = v_ref_2286_;
v___y_2276_ = v___y_2282_;
v___y_2277_ = v___x_2288_;
goto v___jp_2272_;
}
else
{
lean_object* v_val_2289_; 
v_val_2289_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_val_2289_);
lean_dec_ref_known(v___x_2287_, 1);
v___y_2273_ = v___y_2281_;
v___y_2274_ = v___y_2283_;
v___y_2275_ = v_ref_2286_;
v___y_2276_ = v___y_2282_;
v___y_2277_ = v_val_2289_;
goto v___jp_2272_;
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec_ref(v_msgData_2173_);
v_a_2290_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2284_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2284_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
v___jp_2299_:
{
if (v___y_2302_ == 0)
{
v___y_2281_ = v___y_2300_;
v___y_2282_ = v___y_2301_;
v___y_2283_ = v_severity_2174_;
goto v___jp_2280_;
}
else
{
v___y_2281_ = v___y_2300_;
v___y_2282_ = v___y_2301_;
v___y_2283_ = v___x_2298_;
goto v___jp_2280_;
}
}
v___jp_2303_:
{
if (v___y_2304_ == 0)
{
lean_object* v___x_2305_; lean_object* v_scopes_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v_opts_2309_; uint8_t v___x_2310_; uint8_t v___x_2311_; 
v___x_2305_ = lean_st_ref_get(v___y_2177_);
v_scopes_2306_ = lean_ctor_get(v___x_2305_, 2);
lean_inc(v_scopes_2306_);
lean_dec(v___x_2305_);
v___x_2307_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2308_ = l_List_head_x21___redArg(v___x_2307_, v_scopes_2306_);
lean_dec(v_scopes_2306_);
v_opts_2309_ = lean_ctor_get(v___x_2308_, 1);
lean_inc_ref(v_opts_2309_);
lean_dec(v___x_2308_);
v___x_2310_ = 1;
v___x_2311_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2174_, v___x_2310_);
if (v___x_2311_ == 0)
{
lean_dec_ref(v_opts_2309_);
v___y_2300_ = v___y_2304_;
v___y_2301_ = v___y_2304_;
v___y_2302_ = v___x_2311_;
goto v___jp_2299_;
}
else
{
lean_object* v___x_2312_; uint8_t v___x_2313_; 
v___x_2312_ = l_Lean_warningAsError;
v___x_2313_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_2309_, v___x_2312_);
lean_dec_ref(v_opts_2309_);
v___y_2300_ = v___y_2304_;
v___y_2301_ = v___y_2304_;
v___y_2302_ = v___x_2313_;
goto v___jp_2299_;
}
}
else
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
lean_dec_ref(v_msgData_2173_);
v___x_2314_ = lean_box(0);
v___x_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
return v___x_2315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___boxed(lean_object* v_ref_2318_, lean_object* v_msgData_2319_, lean_object* v_severity_2320_, lean_object* v_isSilent_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
uint8_t v_severity_boxed_2325_; uint8_t v_isSilent_boxed_2326_; lean_object* v_res_2327_; 
v_severity_boxed_2325_ = lean_unbox(v_severity_2320_);
v_isSilent_boxed_2326_ = lean_unbox(v_isSilent_2321_);
v_res_2327_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_ref_2318_, v_msgData_2319_, v_severity_boxed_2325_, v_isSilent_boxed_2326_, v___y_2322_, v___y_2323_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v_ref_2318_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(lean_object* v_msgData_2328_, uint8_t v_severity_2329_, uint8_t v_isSilent_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = l_Lean_Elab_Command_getRef___redArg(v___y_2331_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2336_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2336_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_a_2335_, v_msgData_2328_, v_severity_2329_, v_isSilent_2330_, v___y_2331_, v___y_2332_);
lean_dec(v_a_2335_);
return v___x_2336_;
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
lean_dec_ref(v_msgData_2328_);
v_a_2337_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2334_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2334_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26___boxed(lean_object* v_msgData_2345_, lean_object* v_severity_2346_, lean_object* v_isSilent_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
uint8_t v_severity_boxed_2351_; uint8_t v_isSilent_boxed_2352_; lean_object* v_res_2353_; 
v_severity_boxed_2351_ = lean_unbox(v_severity_2346_);
v_isSilent_boxed_2352_ = lean_unbox(v_isSilent_2347_);
v_res_2353_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_2345_, v_severity_boxed_2351_, v_isSilent_boxed_2352_, v___y_2348_, v___y_2349_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object* v_msgData_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
uint8_t v___x_2358_; uint8_t v___x_2359_; lean_object* v___x_2360_; 
v___x_2358_ = 0;
v___x_2359_ = 0;
v___x_2360_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_2354_, v___x_2358_, v___x_2359_, v___y_2355_, v___y_2356_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object* v_msgData_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v_msgData_2361_, v___y_2362_, v___y_2363_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object* v_init_2366_, lean_object* v_x_2367_){
_start:
{
if (lean_obj_tag(v_x_2367_) == 0)
{
lean_object* v_k_2369_; lean_object* v_v_2370_; lean_object* v_l_2371_; lean_object* v_r_2372_; lean_object* v___x_2373_; lean_object* v_a_2374_; lean_object* v_a_2375_; lean_object* v___x_2376_; 
v_k_2369_ = lean_ctor_get(v_x_2367_, 1);
lean_inc(v_k_2369_);
v_v_2370_ = lean_ctor_get(v_x_2367_, 2);
lean_inc(v_v_2370_);
v_l_2371_ = lean_ctor_get(v_x_2367_, 3);
lean_inc(v_l_2371_);
v_r_2372_ = lean_ctor_get(v_x_2367_, 4);
lean_inc(v_r_2372_);
lean_dec_ref_known(v_x_2367_, 5);
v___x_2373_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_2366_, v_l_2371_);
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_a_2374_);
lean_dec_ref(v___x_2373_);
v_a_2375_ = lean_ctor_get(v_a_2374_, 0);
lean_inc(v_a_2375_);
lean_dec(v_a_2374_);
v___x_2376_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2369_, v_v_2370_, v_a_2375_);
v_init_2366_ = v___x_2376_;
v_x_2367_ = v_r_2372_;
goto _start;
}
else
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2378_, 0, v_init_2366_);
v___x_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
return v___x_2379_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object* v_init_2380_, lean_object* v_x_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_2380_, v_x_2381_);
return v_res_2383_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(uint8_t v___x_2384_, lean_object* v_x1_2385_, lean_object* v_x2_2386_){
_start:
{
lean_object* v_fst_2387_; lean_object* v_fst_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; uint8_t v___x_2391_; 
v_fst_2387_ = lean_ctor_get(v_x1_2385_, 0);
lean_inc(v_fst_2387_);
lean_dec_ref(v_x1_2385_);
v_fst_2388_ = lean_ctor_get(v_x2_2386_, 0);
lean_inc(v_fst_2388_);
lean_dec_ref(v_x2_2386_);
v___x_2389_ = l_Lean_Name_toString(v_fst_2387_, v___x_2384_);
v___x_2390_ = l_Lean_Name_toString(v_fst_2388_, v___x_2384_);
v___x_2391_ = lean_string_dec_lt(v___x_2389_, v___x_2390_);
lean_dec_ref(v___x_2390_);
lean_dec_ref(v___x_2389_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0___boxed(lean_object* v___x_2392_, lean_object* v_x1_2393_, lean_object* v_x2_2394_){
_start:
{
uint8_t v___x_18238__boxed_2395_; uint8_t v_res_2396_; lean_object* v_r_2397_; 
v___x_18238__boxed_2395_ = lean_unbox(v___x_2392_);
v_res_2396_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_18238__boxed_2395_, v_x1_2393_, v_x2_2394_);
v_r_2397_ = lean_box(v_res_2396_);
return v_r_2397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(lean_object* v_hi_2398_, lean_object* v_pivot_2399_, lean_object* v_as_2400_, lean_object* v_i_2401_, lean_object* v_k_2402_){
_start:
{
uint8_t v___x_2403_; 
v___x_2403_ = lean_nat_dec_lt(v_k_2402_, v_hi_2398_);
if (v___x_2403_ == 0)
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
lean_dec(v_k_2402_);
lean_dec_ref(v_pivot_2399_);
v___x_2404_ = lean_array_fswap(v_as_2400_, v_i_2401_, v_hi_2398_);
v___x_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2405_, 0, v_i_2401_);
lean_ctor_set(v___x_2405_, 1, v___x_2404_);
return v___x_2405_;
}
else
{
lean_object* v___x_2406_; lean_object* v_fst_2407_; lean_object* v_fst_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; 
v___x_2406_ = lean_array_fget_borrowed(v_as_2400_, v_k_2402_);
v_fst_2407_ = lean_ctor_get(v___x_2406_, 0);
v_fst_2408_ = lean_ctor_get(v_pivot_2399_, 0);
lean_inc(v_fst_2407_);
v___x_2409_ = l_Lean_Name_toString(v_fst_2407_, v___x_2403_);
lean_inc(v_fst_2408_);
v___x_2410_ = l_Lean_Name_toString(v_fst_2408_, v___x_2403_);
v___x_2411_ = lean_string_dec_lt(v___x_2409_, v___x_2410_);
lean_dec_ref(v___x_2410_);
lean_dec_ref(v___x_2409_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2412_ = lean_unsigned_to_nat(1u);
v___x_2413_ = lean_nat_add(v_k_2402_, v___x_2412_);
lean_dec(v_k_2402_);
v_k_2402_ = v___x_2413_;
goto _start;
}
else
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2415_ = lean_array_fswap(v_as_2400_, v_i_2401_, v_k_2402_);
v___x_2416_ = lean_unsigned_to_nat(1u);
v___x_2417_ = lean_nat_add(v_i_2401_, v___x_2416_);
lean_dec(v_i_2401_);
v___x_2418_ = lean_nat_add(v_k_2402_, v___x_2416_);
lean_dec(v_k_2402_);
v_as_2400_ = v___x_2415_;
v_i_2401_ = v___x_2417_;
v_k_2402_ = v___x_2418_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg___boxed(lean_object* v_hi_2420_, lean_object* v_pivot_2421_, lean_object* v_as_2422_, lean_object* v_i_2423_, lean_object* v_k_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_2420_, v_pivot_2421_, v_as_2422_, v_i_2423_, v_k_2424_);
lean_dec(v_hi_2420_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(lean_object* v_n_2426_, lean_object* v_as_2427_, lean_object* v_lo_2428_, lean_object* v_hi_2429_){
_start:
{
lean_object* v___y_2431_; uint8_t v___x_2441_; 
v___x_2441_ = lean_nat_dec_lt(v_lo_2428_, v_hi_2429_);
if (v___x_2441_ == 0)
{
lean_dec(v_lo_2428_);
return v_as_2427_;
}
else
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v_mid_2444_; lean_object* v___y_2446_; lean_object* v___y_2452_; lean_object* v___x_2457_; lean_object* v___x_2458_; uint8_t v___x_2459_; 
v___x_2442_ = lean_nat_add(v_lo_2428_, v_hi_2429_);
v___x_2443_ = lean_unsigned_to_nat(1u);
v_mid_2444_ = lean_nat_shiftr(v___x_2442_, v___x_2443_);
lean_dec(v___x_2442_);
v___x_2457_ = lean_array_fget_borrowed(v_as_2427_, v_mid_2444_);
v___x_2458_ = lean_array_fget_borrowed(v_as_2427_, v_lo_2428_);
lean_inc(v___x_2458_);
lean_inc(v___x_2457_);
v___x_2459_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2441_, v___x_2457_, v___x_2458_);
if (v___x_2459_ == 0)
{
v___y_2452_ = v_as_2427_;
goto v___jp_2451_;
}
else
{
lean_object* v___x_2460_; 
v___x_2460_ = lean_array_fswap(v_as_2427_, v_lo_2428_, v_mid_2444_);
v___y_2452_ = v___x_2460_;
goto v___jp_2451_;
}
v___jp_2445_:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; uint8_t v___x_2449_; 
v___x_2447_ = lean_array_fget_borrowed(v___y_2446_, v_mid_2444_);
v___x_2448_ = lean_array_fget_borrowed(v___y_2446_, v_hi_2429_);
lean_inc(v___x_2448_);
lean_inc(v___x_2447_);
v___x_2449_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2441_, v___x_2447_, v___x_2448_);
if (v___x_2449_ == 0)
{
lean_dec(v_mid_2444_);
v___y_2431_ = v___y_2446_;
goto v___jp_2430_;
}
else
{
lean_object* v___x_2450_; 
v___x_2450_ = lean_array_fswap(v___y_2446_, v_mid_2444_, v_hi_2429_);
lean_dec(v_mid_2444_);
v___y_2431_ = v___x_2450_;
goto v___jp_2430_;
}
}
v___jp_2451_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; uint8_t v___x_2455_; 
v___x_2453_ = lean_array_fget_borrowed(v___y_2452_, v_hi_2429_);
v___x_2454_ = lean_array_fget_borrowed(v___y_2452_, v_lo_2428_);
lean_inc(v___x_2454_);
lean_inc(v___x_2453_);
v___x_2455_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2441_, v___x_2453_, v___x_2454_);
if (v___x_2455_ == 0)
{
v___y_2446_ = v___y_2452_;
goto v___jp_2445_;
}
else
{
lean_object* v___x_2456_; 
v___x_2456_ = lean_array_fswap(v___y_2452_, v_lo_2428_, v_hi_2429_);
v___y_2446_ = v___x_2456_;
goto v___jp_2445_;
}
}
}
v___jp_2430_:
{
lean_object* v_pivot_2432_; lean_object* v___x_2433_; lean_object* v_fst_2434_; lean_object* v_snd_2435_; uint8_t v___x_2436_; 
v_pivot_2432_ = lean_array_fget(v___y_2431_, v_hi_2429_);
lean_inc_n(v_lo_2428_, 2);
v___x_2433_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_2429_, v_pivot_2432_, v___y_2431_, v_lo_2428_, v_lo_2428_);
v_fst_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_fst_2434_);
v_snd_2435_ = lean_ctor_get(v___x_2433_, 1);
lean_inc(v_snd_2435_);
lean_dec_ref(v___x_2433_);
v___x_2436_ = lean_nat_dec_le(v_hi_2429_, v_fst_2434_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2437_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_2426_, v_snd_2435_, v_lo_2428_, v_fst_2434_);
v___x_2438_ = lean_unsigned_to_nat(1u);
v___x_2439_ = lean_nat_add(v_fst_2434_, v___x_2438_);
lean_dec(v_fst_2434_);
v_as_2427_ = v___x_2437_;
v_lo_2428_ = v___x_2439_;
goto _start;
}
else
{
lean_dec(v_fst_2434_);
lean_dec(v_lo_2428_);
return v_snd_2435_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___boxed(lean_object* v_n_2461_, lean_object* v_as_2462_, lean_object* v_lo_2463_, lean_object* v_hi_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_2461_, v_as_2462_, v_lo_2463_, v_hi_2464_);
lean_dec(v_hi_2464_);
lean_dec(v_n_2461_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(lean_object* v_init_2466_, lean_object* v_x_2467_){
_start:
{
if (lean_obj_tag(v_x_2467_) == 0)
{
lean_object* v_k_2468_; lean_object* v_v_2469_; lean_object* v_l_2470_; lean_object* v_r_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v_k_2468_ = lean_ctor_get(v_x_2467_, 1);
v_v_2469_ = lean_ctor_get(v_x_2467_, 2);
v_l_2470_ = lean_ctor_get(v_x_2467_, 3);
v_r_2471_ = lean_ctor_get(v_x_2467_, 4);
v___x_2472_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_2466_, v_l_2470_);
lean_inc(v_v_2469_);
lean_inc(v_k_2468_);
v___x_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2473_, 0, v_k_2468_);
lean_ctor_set(v___x_2473_, 1, v_v_2469_);
v___x_2474_ = lean_array_push(v___x_2472_, v___x_2473_);
v_init_2466_ = v___x_2474_;
v_x_2467_ = v_r_2471_;
goto _start;
}
else
{
return v_init_2466_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25___boxed(lean_object* v_init_2476_, lean_object* v_x_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_2476_, v_x_2477_);
lean_dec(v_x_2477_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(lean_object* v_as_2479_, size_t v_sz_2480_, size_t v_i_2481_, lean_object* v_b_2482_){
_start:
{
uint8_t v___x_2484_; 
v___x_2484_ = lean_usize_dec_lt(v_i_2481_, v_sz_2480_);
if (v___x_2484_ == 0)
{
lean_object* v___x_2485_; 
v___x_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2485_, 0, v_b_2482_);
return v___x_2485_;
}
else
{
lean_object* v_a_2486_; lean_object* v_fst_2487_; lean_object* v_snd_2488_; lean_object* v_found_2489_; size_t v___x_2490_; size_t v___x_2491_; 
v_a_2486_ = lean_array_uget_borrowed(v_as_2479_, v_i_2481_);
v_fst_2487_ = lean_ctor_get(v_a_2486_, 0);
v_snd_2488_ = lean_ctor_get(v_a_2486_, 1);
lean_inc(v_snd_2488_);
lean_inc(v_fst_2487_);
v_found_2489_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2487_, v_snd_2488_, v_b_2482_);
v___x_2490_ = ((size_t)1ULL);
v___x_2491_ = lean_usize_add(v_i_2481_, v___x_2490_);
v_i_2481_ = v___x_2491_;
v_b_2482_ = v_found_2489_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg___boxed(lean_object* v_as_2493_, lean_object* v_sz_2494_, lean_object* v_i_2495_, lean_object* v_b_2496_, lean_object* v___y_2497_){
_start:
{
size_t v_sz_boxed_2498_; size_t v_i_boxed_2499_; lean_object* v_res_2500_; 
v_sz_boxed_2498_ = lean_unbox_usize(v_sz_2494_);
lean_dec(v_sz_2494_);
v_i_boxed_2499_ = lean_unbox_usize(v_i_2495_);
lean_dec(v_i_2495_);
v_res_2500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_2493_, v_sz_boxed_2498_, v_i_boxed_2499_, v_b_2496_);
lean_dec_ref(v_as_2493_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object* v_as_2501_, size_t v_sz_2502_, size_t v_i_2503_, lean_object* v_b_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
uint8_t v___x_2508_; 
v___x_2508_ = lean_usize_dec_lt(v_i_2503_, v_sz_2502_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v_b_2504_);
return v___x_2509_;
}
else
{
lean_object* v_a_2510_; size_t v_sz_2511_; size_t v___x_2512_; lean_object* v___x_2513_; 
v_a_2510_ = lean_array_uget_borrowed(v_as_2501_, v_i_2503_);
v_sz_2511_ = lean_array_size(v_a_2510_);
v___x_2512_ = ((size_t)0ULL);
v___x_2513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_a_2510_, v_sz_2511_, v___x_2512_, v_b_2504_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; size_t v___x_2515_; size_t v___x_2516_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_a_2514_);
lean_dec_ref_known(v___x_2513_, 1);
v___x_2515_ = ((size_t)1ULL);
v___x_2516_ = lean_usize_add(v_i_2503_, v___x_2515_);
v_i_2503_ = v___x_2516_;
v_b_2504_ = v_a_2514_;
goto _start;
}
else
{
return v___x_2513_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object* v_as_2518_, lean_object* v_sz_2519_, lean_object* v_i_2520_, lean_object* v_b_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
size_t v_sz_boxed_2525_; size_t v_i_boxed_2526_; lean_object* v_res_2527_; 
v_sz_boxed_2525_ = lean_unbox_usize(v_sz_2519_);
lean_dec(v_sz_2519_);
v_i_boxed_2526_ = lean_unbox_usize(v_i_2520_);
lean_dec(v_i_2520_);
v_res_2527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_as_2518_, v_sz_boxed_2525_, v_i_boxed_2526_, v_b_2521_, v___y_2522_, v___y_2523_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec_ref(v_as_2518_);
return v_res_2527_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = lean_box(1);
v___x_2529_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2528_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v___y_2536_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___x_2551_; lean_object* v_env_2552_; lean_object* v___x_2553_; lean_object* v_toEnvExtension_2554_; lean_object* v_asyncMode_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v_a_2561_; lean_object* v_a_2563_; lean_object* v_a_2586_; 
v___x_2551_ = lean_st_ref_get(v___y_2533_);
v_env_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc_ref_n(v_env_2552_, 2);
lean_dec(v___x_2551_);
v___x_2553_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2554_ = lean_ctor_get(v___x_2553_, 0);
v_asyncMode_2555_ = lean_ctor_get(v_toEnvExtension_2554_, 2);
v___x_2556_ = lean_box(1);
v___x_2557_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0, &l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0);
v___x_2558_ = lean_box(0);
v___x_2559_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2556_, v___x_2553_, v_env_2552_, v_asyncMode_2555_, v___x_2558_);
v___x_2560_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v___x_2556_, v___x_2559_);
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc(v_a_2561_);
lean_dec_ref(v___x_2560_);
v_a_2586_ = lean_ctor_get(v_a_2561_, 0);
lean_inc(v_a_2586_);
lean_dec(v_a_2561_);
v_a_2563_ = v_a_2586_;
goto v___jp_2562_;
v___jp_2535_:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = lean_array_to_list(v___y_2536_);
v___x_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2537_);
return v___x_2538_;
}
v___jp_2539_:
{
lean_object* v___x_2544_; 
v___x_2544_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v___y_2541_, v___y_2542_, v___y_2540_, v___y_2543_);
lean_dec(v___y_2543_);
lean_dec(v___y_2541_);
v___y_2536_ = v___x_2544_;
goto v___jp_2535_;
}
v___jp_2545_:
{
uint8_t v___x_2550_; 
v___x_2550_ = lean_nat_dec_le(v___y_2549_, v___y_2546_);
if (v___x_2550_ == 0)
{
lean_dec(v___y_2546_);
lean_inc(v___y_2549_);
v___y_2540_ = v___y_2549_;
v___y_2541_ = v___y_2547_;
v___y_2542_ = v___y_2548_;
v___y_2543_ = v___y_2549_;
goto v___jp_2539_;
}
else
{
v___y_2540_ = v___y_2549_;
v___y_2541_ = v___y_2547_;
v___y_2542_ = v___y_2548_;
v___y_2543_ = v___y_2546_;
goto v___jp_2539_;
}
}
v___jp_2562_:
{
lean_object* v___x_2564_; lean_object* v_importedEntries_2565_; size_t v_sz_2566_; size_t v___x_2567_; lean_object* v___x_2568_; 
v___x_2564_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2557_, v_toEnvExtension_2554_, v_env_2552_, v_asyncMode_2555_, v___x_2558_);
v_importedEntries_2565_ = lean_ctor_get(v___x_2564_, 0);
lean_inc_ref(v_importedEntries_2565_);
lean_dec(v___x_2564_);
v_sz_2566_ = lean_array_size(v_importedEntries_2565_);
v___x_2567_ = ((size_t)0ULL);
v___x_2568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_importedEntries_2565_, v_sz_2566_, v___x_2567_, v_a_2563_, v___y_2532_, v___y_2533_);
lean_dec_ref(v_importedEntries_2565_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v_arr_2572_; lean_object* v___x_2573_; uint8_t v___x_2574_; 
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_a_2569_);
lean_dec_ref_known(v___x_2568_, 1);
v___x_2570_ = lean_unsigned_to_nat(0u);
v___x_2571_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1));
v_arr_2572_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v___x_2571_, v_a_2569_);
lean_dec(v_a_2569_);
v___x_2573_ = lean_array_get_size(v_arr_2572_);
v___x_2574_ = lean_nat_dec_eq(v___x_2573_, v___x_2570_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2575_; lean_object* v___x_2576_; uint8_t v___x_2577_; 
v___x_2575_ = lean_unsigned_to_nat(1u);
v___x_2576_ = lean_nat_sub(v___x_2573_, v___x_2575_);
v___x_2577_ = lean_nat_dec_le(v___x_2570_, v___x_2576_);
if (v___x_2577_ == 0)
{
lean_inc(v___x_2576_);
v___y_2546_ = v___x_2576_;
v___y_2547_ = v___x_2573_;
v___y_2548_ = v_arr_2572_;
v___y_2549_ = v___x_2576_;
goto v___jp_2545_;
}
else
{
v___y_2546_ = v___x_2576_;
v___y_2547_ = v___x_2573_;
v___y_2548_ = v_arr_2572_;
v___y_2549_ = v___x_2570_;
goto v___jp_2545_;
}
}
else
{
v___y_2536_ = v_arr_2572_;
goto v___jp_2535_;
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
v_a_2578_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2568_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2568_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v___y_2587_, v___y_2588_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object* v_t_2591_, lean_object* v_k_2592_, lean_object* v_fallback_2593_){
_start:
{
if (lean_obj_tag(v_t_2591_) == 0)
{
lean_object* v_k_2594_; lean_object* v_v_2595_; lean_object* v_l_2596_; lean_object* v_r_2597_; uint8_t v___x_2598_; 
v_k_2594_ = lean_ctor_get(v_t_2591_, 1);
v_v_2595_ = lean_ctor_get(v_t_2591_, 2);
v_l_2596_ = lean_ctor_get(v_t_2591_, 3);
v_r_2597_ = lean_ctor_get(v_t_2591_, 4);
v___x_2598_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2592_, v_k_2594_);
switch(v___x_2598_)
{
case 0:
{
v_t_2591_ = v_l_2596_;
goto _start;
}
case 1:
{
lean_inc(v_v_2595_);
return v_v_2595_;
}
default: 
{
v_t_2591_ = v_r_2597_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2593_);
return v_fallback_2593_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object* v_t_2601_, lean_object* v_k_2602_, lean_object* v_fallback_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_2601_, v_k_2602_, v_fallback_2603_);
lean_dec(v_fallback_2603_);
lean_dec(v_k_2602_);
lean_dec(v_t_2601_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object* v_as_2605_, size_t v_sz_2606_, size_t v_i_2607_, lean_object* v_b_2608_){
_start:
{
uint8_t v___x_2610_; 
v___x_2610_ = lean_usize_dec_lt(v_i_2607_, v_sz_2606_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; 
v___x_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2611_, 0, v_b_2608_);
return v___x_2611_;
}
else
{
lean_object* v_a_2612_; lean_object* v_fst_2613_; lean_object* v_snd_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; size_t v___x_2619_; size_t v___x_2620_; 
v_a_2612_ = lean_array_uget_borrowed(v_as_2605_, v_i_2607_);
v_fst_2613_ = lean_ctor_get(v_a_2612_, 0);
v_snd_2614_ = lean_ctor_get(v_a_2612_, 1);
v___x_2615_ = l_Lean_NameSet_empty;
v___x_2616_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_2608_, v_snd_2614_, v___x_2615_);
lean_inc(v_fst_2613_);
v___x_2617_ = l_Lean_NameSet_insert(v___x_2616_, v_fst_2613_);
lean_inc(v_snd_2614_);
v___x_2618_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_snd_2614_, v___x_2617_, v_b_2608_);
v___x_2619_ = ((size_t)1ULL);
v___x_2620_ = lean_usize_add(v_i_2607_, v___x_2619_);
v_i_2607_ = v___x_2620_;
v_b_2608_ = v___x_2618_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object* v_as_2622_, lean_object* v_sz_2623_, lean_object* v_i_2624_, lean_object* v_b_2625_, lean_object* v___y_2626_){
_start:
{
size_t v_sz_boxed_2627_; size_t v_i_boxed_2628_; lean_object* v_res_2629_; 
v_sz_boxed_2627_ = lean_unbox_usize(v_sz_2623_);
lean_dec(v_sz_2623_);
v_i_boxed_2628_ = lean_unbox_usize(v_i_2624_);
lean_dec(v_i_2624_);
v_res_2629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_2622_, v_sz_boxed_2627_, v_i_boxed_2628_, v_b_2625_);
lean_dec_ref(v_as_2622_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object* v_as_2630_, size_t v_sz_2631_, size_t v_i_2632_, lean_object* v_b_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
uint8_t v___x_2637_; 
v___x_2637_ = lean_usize_dec_lt(v_i_2632_, v_sz_2631_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; 
v___x_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2638_, 0, v_b_2633_);
return v___x_2638_;
}
else
{
lean_object* v_a_2639_; size_t v_sz_2640_; size_t v___x_2641_; lean_object* v___x_2642_; 
v_a_2639_ = lean_array_uget_borrowed(v_as_2630_, v_i_2632_);
v_sz_2640_ = lean_array_size(v_a_2639_);
v___x_2641_ = ((size_t)0ULL);
v___x_2642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_a_2639_, v_sz_2640_, v___x_2641_, v_b_2633_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; size_t v___x_2644_; size_t v___x_2645_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___x_2642_, 1);
v___x_2644_ = ((size_t)1ULL);
v___x_2645_ = lean_usize_add(v_i_2632_, v___x_2644_);
v_i_2632_ = v___x_2645_;
v_b_2633_ = v_a_2643_;
goto _start;
}
else
{
return v___x_2642_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object* v_as_2647_, lean_object* v_sz_2648_, lean_object* v_i_2649_, lean_object* v_b_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
size_t v_sz_boxed_2654_; size_t v_i_boxed_2655_; lean_object* v_res_2656_; 
v_sz_boxed_2654_ = lean_unbox_usize(v_sz_2648_);
lean_dec(v_sz_2648_);
v_i_boxed_2655_ = lean_unbox_usize(v_i_2649_);
lean_dec(v_i_2649_);
v_res_2656_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v_as_2647_, v_sz_boxed_2654_, v_i_boxed_2655_, v_b_2650_, v___y_2651_, v___y_2652_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec_ref(v_as_2647_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object* v_as_2657_, size_t v_i_2658_, size_t v_stop_2659_, lean_object* v_b_2660_){
_start:
{
uint8_t v___x_2661_; 
v___x_2661_ = lean_usize_dec_eq(v_i_2658_, v_stop_2659_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; lean_object* v_fst_2663_; lean_object* v_snd_2664_; lean_object* v___x_2665_; size_t v___x_2666_; size_t v___x_2667_; 
v___x_2662_ = lean_array_uget_borrowed(v_as_2657_, v_i_2658_);
v_fst_2663_ = lean_ctor_get(v___x_2662_, 0);
v_snd_2664_ = lean_ctor_get(v___x_2662_, 1);
lean_inc(v_snd_2664_);
lean_inc(v_fst_2663_);
v___x_2665_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2663_, v_snd_2664_, v_b_2660_);
v___x_2666_ = ((size_t)1ULL);
v___x_2667_ = lean_usize_add(v_i_2658_, v___x_2666_);
v_i_2658_ = v___x_2667_;
v_b_2660_ = v___x_2665_;
goto _start;
}
else
{
return v_b_2660_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object* v_as_2669_, lean_object* v_i_2670_, lean_object* v_stop_2671_, lean_object* v_b_2672_){
_start:
{
size_t v_i_boxed_2673_; size_t v_stop_boxed_2674_; lean_object* v_res_2675_; 
v_i_boxed_2673_ = lean_unbox_usize(v_i_2670_);
lean_dec(v_i_2670_);
v_stop_boxed_2674_ = lean_unbox_usize(v_stop_2671_);
lean_dec(v_stop_2671_);
v_res_2675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v_as_2669_, v_i_boxed_2673_, v_stop_boxed_2674_, v_b_2672_);
lean_dec_ref(v_as_2669_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object* v_as_2676_, size_t v_i_2677_, size_t v_stop_2678_, lean_object* v_b_2679_){
_start:
{
lean_object* v___y_2681_; uint8_t v___x_2685_; 
v___x_2685_ = lean_usize_dec_eq(v_i_2677_, v_stop_2678_);
if (v___x_2685_ == 0)
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; uint8_t v___x_2689_; 
v___x_2686_ = lean_array_uget_borrowed(v_as_2676_, v_i_2677_);
v___x_2687_ = lean_unsigned_to_nat(0u);
v___x_2688_ = lean_array_get_size(v___x_2686_);
v___x_2689_ = lean_nat_dec_lt(v___x_2687_, v___x_2688_);
if (v___x_2689_ == 0)
{
v___y_2681_ = v_b_2679_;
goto v___jp_2680_;
}
else
{
size_t v___x_2690_; size_t v___x_2691_; lean_object* v___x_2692_; 
v___x_2690_ = ((size_t)0ULL);
v___x_2691_ = lean_usize_of_nat(v___x_2688_);
v___x_2692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_2686_, v___x_2690_, v___x_2691_, v_b_2679_);
v___y_2681_ = v___x_2692_;
goto v___jp_2680_;
}
}
else
{
return v_b_2679_;
}
v___jp_2680_:
{
size_t v___x_2682_; size_t v___x_2683_; 
v___x_2682_ = ((size_t)1ULL);
v___x_2683_ = lean_usize_add(v_i_2677_, v___x_2682_);
v_i_2677_ = v___x_2683_;
v_b_2679_ = v___y_2681_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object* v_as_2693_, lean_object* v_i_2694_, lean_object* v_stop_2695_, lean_object* v_b_2696_){
_start:
{
size_t v_i_boxed_2697_; size_t v_stop_boxed_2698_; lean_object* v_res_2699_; 
v_i_boxed_2697_ = lean_unbox_usize(v_i_2694_);
lean_dec(v_i_2694_);
v_stop_boxed_2698_ = lean_unbox_usize(v_stop_2695_);
lean_dec(v_stop_2695_);
v_res_2699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v_as_2693_, v_i_boxed_2697_, v_stop_boxed_2698_, v_b_2696_);
lean_dec_ref(v_as_2693_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object* v___y_2700_){
_start:
{
lean_object* v___x_2702_; lean_object* v_env_2703_; lean_object* v___x_2704_; lean_object* v_ext_2705_; lean_object* v_toEnvExtension_2706_; lean_object* v_asyncMode_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v_categories_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2702_ = lean_st_ref_get(v___y_2700_);
v_env_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc_ref_n(v_env_2703_, 2);
lean_dec(v___x_2702_);
v___x_2704_ = l_Lean_Parser_parserExtension;
v_ext_2705_ = lean_ctor_get(v___x_2704_, 1);
v_toEnvExtension_2706_ = lean_ctor_get(v_ext_2705_, 0);
v_asyncMode_2707_ = lean_ctor_get(v_toEnvExtension_2706_, 2);
v___x_2708_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2709_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2708_, v___x_2704_, v_env_2703_, v_asyncMode_2707_);
v_categories_2710_ = lean_ctor_get(v___x_2709_, 2);
lean_inc_ref(v_categories_2710_);
lean_dec(v___x_2709_);
v___x_2711_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_2712_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_2710_, v___x_2711_);
lean_dec_ref(v_categories_2710_);
if (lean_obj_tag(v___x_2712_) == 1)
{
lean_object* v_val_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2746_; 
v_val_2713_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2715_ = v___x_2712_;
v_isShared_2716_ = v_isSharedCheck_2746_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_val_2713_);
lean_dec(v___x_2712_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2746_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___y_2718_; lean_object* v___x_2727_; lean_object* v_toEnvExtension_2728_; lean_object* v_exportEntriesFn_2729_; lean_object* v_asyncMode_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v_importedEntries_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v_exported_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; uint8_t v___x_2742_; 
v___x_2727_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_2728_ = lean_ctor_get(v___x_2727_, 0);
v_exportEntriesFn_2729_ = lean_ctor_get(v___x_2727_, 4);
v_asyncMode_2730_ = lean_ctor_get(v_toEnvExtension_2728_, 2);
v___x_2731_ = lean_box(1);
v___x_2732_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_2733_ = lean_box(0);
lean_inc_ref_n(v_env_2703_, 2);
v___x_2734_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2732_, v_toEnvExtension_2728_, v_env_2703_, v_asyncMode_2730_, v___x_2733_);
v_importedEntries_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc_ref(v_importedEntries_2735_);
lean_dec(v___x_2734_);
v___x_2736_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2731_, v___x_2727_, v_env_2703_, v_asyncMode_2730_, v___x_2733_);
lean_inc_ref(v_exportEntriesFn_2729_);
v___x_2737_ = lean_apply_2(v_exportEntriesFn_2729_, v_env_2703_, v___x_2736_);
v_exported_2738_ = lean_ctor_get(v___x_2737_, 0);
lean_inc(v_exported_2738_);
lean_dec_ref(v___x_2737_);
v___x_2739_ = lean_array_push(v_importedEntries_2735_, v_exported_2738_);
v___x_2740_ = lean_unsigned_to_nat(0u);
v___x_2741_ = lean_array_get_size(v___x_2739_);
v___x_2742_ = lean_nat_dec_lt(v___x_2740_, v___x_2741_);
if (v___x_2742_ == 0)
{
lean_dec_ref(v___x_2739_);
v___y_2718_ = v___x_2731_;
goto v___jp_2717_;
}
else
{
size_t v___x_2743_; size_t v___x_2744_; lean_object* v___x_2745_; 
v___x_2743_ = ((size_t)0ULL);
v___x_2744_ = lean_usize_of_nat(v___x_2741_);
v___x_2745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_2739_, v___x_2743_, v___x_2744_, v___x_2731_);
lean_dec_ref(v___x_2739_);
v___y_2718_ = v___x_2745_;
goto v___jp_2717_;
}
v___jp_2717_:
{
lean_object* v_tables_2719_; lean_object* v_leadingTable_2720_; lean_object* v_trailingTable_2721_; lean_object* v_firstTokens_2722_; lean_object* v_firstTokens_2723_; lean_object* v___x_2725_; 
v_tables_2719_ = lean_ctor_get(v_val_2713_, 2);
v_leadingTable_2720_ = lean_ctor_get(v_tables_2719_, 0);
v_trailingTable_2721_ = lean_ctor_get(v_tables_2719_, 2);
lean_inc(v_trailingTable_2721_);
lean_inc(v_leadingTable_2720_);
lean_inc(v_val_2713_);
v_firstTokens_2722_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2713_, v_leadingTable_2720_, v___y_2718_);
v_firstTokens_2723_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2713_, v_trailingTable_2721_, v_firstTokens_2722_);
if (v_isShared_2716_ == 0)
{
lean_ctor_set_tag(v___x_2715_, 0);
lean_ctor_set(v___x_2715_, 0, v_firstTokens_2723_);
v___x_2725_ = v___x_2715_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_firstTokens_2723_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
else
{
lean_object* v___x_2747_; lean_object* v___x_2748_; 
lean_dec(v___x_2712_);
lean_dec_ref(v_env_2703_);
v___x_2747_ = lean_box(1);
v___x_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2747_);
return v___x_2748_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_2749_);
lean_dec(v___y_2749_);
return v_res_2751_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0(void){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2752_ = lean_box(1);
v___x_2753_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2752_);
return v___x_2753_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2(void){
_start:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1));
v___x_2756_ = l_Lean_stringToMessageData(v___x_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v_env_2763_; lean_object* v_env_2764_; lean_object* v_env_2765_; lean_object* v___x_2766_; lean_object* v_toEnvExtension_2767_; lean_object* v_exportEntriesFn_2768_; lean_object* v_asyncMode_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v_importedEntries_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2826_; 
v___x_2760_ = lean_st_ref_get(v_a_2758_);
v___x_2761_ = lean_st_ref_get(v_a_2758_);
v___x_2762_ = lean_st_ref_get(v_a_2758_);
v_env_2763_ = lean_ctor_get(v___x_2760_, 0);
lean_inc_ref(v_env_2763_);
lean_dec(v___x_2760_);
v_env_2764_ = lean_ctor_get(v___x_2761_, 0);
lean_inc_ref(v_env_2764_);
lean_dec(v___x_2761_);
v_env_2765_ = lean_ctor_get(v___x_2762_, 0);
lean_inc_ref(v_env_2765_);
lean_dec(v___x_2762_);
v___x_2766_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_2767_ = lean_ctor_get(v___x_2766_, 0);
v_exportEntriesFn_2768_ = lean_ctor_get(v___x_2766_, 4);
v_asyncMode_2769_ = lean_ctor_get(v_toEnvExtension_2767_, 2);
v___x_2770_ = lean_box(1);
v___x_2771_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_2772_ = lean_box(0);
v___x_2773_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2771_, v_toEnvExtension_2767_, v_env_2763_, v_asyncMode_2769_, v___x_2772_);
v_importedEntries_2774_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2826_ == 0)
{
lean_object* v_unused_2827_; 
v_unused_2827_ = lean_ctor_get(v___x_2773_, 1);
lean_dec(v_unused_2827_);
v___x_2776_ = v___x_2773_;
v_isShared_2777_ = v_isSharedCheck_2826_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_importedEntries_2774_);
lean_dec(v___x_2773_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2826_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v_exported_2780_; lean_object* v___x_2781_; size_t v_sz_2782_; size_t v___x_2783_; lean_object* v___x_2784_; 
v___x_2778_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2770_, v___x_2766_, v_env_2765_, v_asyncMode_2769_, v___x_2772_);
lean_inc_ref(v_exportEntriesFn_2768_);
v___x_2779_ = lean_apply_2(v_exportEntriesFn_2768_, v_env_2764_, v___x_2778_);
v_exported_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_exported_2780_);
lean_dec_ref(v___x_2779_);
v___x_2781_ = lean_array_push(v_importedEntries_2774_, v_exported_2780_);
v_sz_2782_ = lean_array_size(v___x_2781_);
v___x_2783_ = ((size_t)0ULL);
v___x_2784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v___x_2781_, v_sz_2782_, v___x_2783_, v___x_2770_, v_a_2757_, v_a_2758_);
lean_dec_ref(v___x_2781_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; lean_object* v___x_2786_; lean_object* v_a_2787_; lean_object* v___x_2788_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2785_);
lean_dec_ref_known(v___x_2784_, 1);
v___x_2786_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v_a_2758_);
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref(v___x_2786_);
v___x_2788_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v_a_2757_, v_a_2758_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2788_, 1);
v___x_2790_ = lean_box(0);
v___x_2791_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_2787_, v_a_2785_, v_a_2789_, v___x_2790_, v_a_2757_, v_a_2758_);
lean_dec(v_a_2785_);
lean_dec(v_a_2787_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2797_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2792_);
lean_dec_ref_known(v___x_2791_, 1);
v___x_2793_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2);
v___x_2794_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2795_ = l_Lean_MessageData_joinSep(v_a_2792_, v___x_2794_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set_tag(v___x_2776_, 7);
lean_ctor_set(v___x_2776_, 1, v___x_2795_);
lean_ctor_set(v___x_2776_, 0, v___x_2794_);
v___x_2797_ = v___x_2776_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2794_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v___x_2795_);
v___x_2797_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2798_ = l_Lean_MessageData_nestD(v___x_2797_);
v___x_2799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2793_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
v___x_2800_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v___x_2799_, v_a_2757_, v_a_2758_);
return v___x_2800_;
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_del_object(v___x_2776_);
v_a_2802_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2791_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2791_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
else
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
lean_dec(v_a_2787_);
lean_dec(v_a_2785_);
lean_del_object(v___x_2776_);
v_a_2810_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2788_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2788_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_del_object(v___x_2776_);
v_a_2818_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2784_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2784_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_2828_, v_a_2829_);
lean_dec(v_a_2829_);
lean_dec_ref(v_a_2828_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object* v___stx_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_2833_, v_a_2834_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object* v___stx_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags(v___stx_2837_, v_a_2838_, v_a_2839_);
lean_dec(v_a_2839_);
lean_dec_ref(v_a_2838_);
lean_dec(v___stx_2837_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object* v_00_u03b4_2842_, lean_object* v_t_2843_, lean_object* v_k_2844_, lean_object* v_fallback_2845_){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_2843_, v_k_2844_, v_fallback_2845_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object* v_00_u03b4_2847_, lean_object* v_t_2848_, lean_object* v_k_2849_, lean_object* v_fallback_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(v_00_u03b4_2847_, v_t_2848_, v_k_2849_, v_fallback_2850_);
lean_dec(v_fallback_2850_);
lean_dec(v_k_2849_);
lean_dec(v_t_2848_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object* v_as_2852_, size_t v_sz_2853_, size_t v_i_2854_, lean_object* v_b_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v___x_2859_; 
v___x_2859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_2852_, v_sz_2853_, v_i_2854_, v_b_2855_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object* v_as_2860_, lean_object* v_sz_2861_, lean_object* v_i_2862_, lean_object* v_b_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
size_t v_sz_boxed_2867_; size_t v_i_boxed_2868_; lean_object* v_res_2869_; 
v_sz_boxed_2867_ = lean_unbox_usize(v_sz_2861_);
lean_dec(v_sz_2861_);
v_i_boxed_2868_ = lean_unbox_usize(v_i_2862_);
lean_dec(v_i_2862_);
v_res_2869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(v_as_2860_, v_sz_boxed_2867_, v_i_boxed_2868_, v_b_2863_, v___y_2864_, v___y_2865_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec_ref(v_as_2860_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_2871_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(v___y_2874_, v___y_2875_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object* v_val_2878_, lean_object* v___x_2879_, lean_object* v___x_2880_, lean_object* v_inst_2881_, lean_object* v_R_2882_, lean_object* v_a_2883_, lean_object* v_b_2884_){
_start:
{
lean_object* v___x_2885_; 
v___x_2885_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2878_, v___x_2879_, v___x_2880_, v_a_2883_, v_b_2884_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object* v_val_2886_, lean_object* v___x_2887_, lean_object* v___x_2888_, lean_object* v_inst_2889_, lean_object* v_R_2890_, lean_object* v_a_2891_, lean_object* v_b_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(v_val_2886_, v___x_2887_, v___x_2888_, v_inst_2889_, v_R_2890_, v_a_2891_, v_b_2892_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v_val_2886_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object* v_init_2894_, lean_object* v_t_2895_){
_start:
{
lean_object* v___x_2896_; 
v___x_2896_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_2894_, v_t_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object* v_n_2897_, lean_object* v_as_2898_, lean_object* v_lo_2899_, lean_object* v_hi_2900_, lean_object* v_w_2901_, lean_object* v_hlo_2902_, lean_object* v_hhi_2903_){
_start:
{
lean_object* v___x_2904_; 
v___x_2904_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_2897_, v_as_2898_, v_lo_2899_, v_hi_2900_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object* v_n_2905_, lean_object* v_as_2906_, lean_object* v_lo_2907_, lean_object* v_hi_2908_, lean_object* v_w_2909_, lean_object* v_hlo_2910_, lean_object* v_hhi_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(v_n_2905_, v_as_2906_, v_lo_2907_, v_hi_2908_, v_w_2909_, v_hlo_2910_, v_hhi_2911_);
lean_dec(v_hi_2908_);
lean_dec(v_n_2905_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object* v_00_u03b2_2913_, lean_object* v_x_2914_, lean_object* v_x_2915_){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_2914_, v_x_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2917_, lean_object* v_x_2918_, lean_object* v_x_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(v_00_u03b2_2917_, v_x_2918_, v_x_2919_);
lean_dec(v_x_2919_);
lean_dec_ref(v_x_2918_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object* v_tac_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_2921_, v___y_2923_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object* v_tac_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(v_tac_2926_, v___y_2927_, v___y_2928_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object* v_00_u03b4_2931_, lean_object* v_t_2932_, lean_object* v_k_2933_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_2932_, v_k_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___boxed(lean_object* v_00_u03b4_2935_, lean_object* v_t_2936_, lean_object* v_k_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(v_00_u03b4_2935_, v_t_2936_, v_k_2937_);
lean_dec(v_k_2937_);
lean_dec(v_t_2936_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object* v_00_u03b2_2939_, lean_object* v_x_2940_, lean_object* v_x_2941_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_2940_, v_x_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object* v_00_u03b2_2943_, lean_object* v_x_2944_, lean_object* v_x_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(v_00_u03b2_2943_, v_x_2944_, v_x_2945_);
lean_dec(v_x_2945_);
lean_dec_ref(v_x_2944_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(lean_object* v_n_2947_, lean_object* v_lo_2948_, lean_object* v_hi_2949_, lean_object* v_hhi_2950_, lean_object* v_pivot_2951_, lean_object* v_as_2952_, lean_object* v_i_2953_, lean_object* v_k_2954_, lean_object* v_ilo_2955_, lean_object* v_ik_2956_, lean_object* v_w_2957_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_2949_, v_pivot_2951_, v_as_2952_, v_i_2953_, v_k_2954_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___boxed(lean_object* v_n_2959_, lean_object* v_lo_2960_, lean_object* v_hi_2961_, lean_object* v_hhi_2962_, lean_object* v_pivot_2963_, lean_object* v_as_2964_, lean_object* v_i_2965_, lean_object* v_k_2966_, lean_object* v_ilo_2967_, lean_object* v_ik_2968_, lean_object* v_w_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(v_n_2959_, v_lo_2960_, v_hi_2961_, v_hhi_2962_, v_pivot_2963_, v_as_2964_, v_i_2965_, v_k_2966_, v_ilo_2967_, v_ik_2968_, v_w_2969_);
lean_dec(v_hi_2961_);
lean_dec(v_lo_2960_);
lean_dec(v_n_2959_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(lean_object* v_as_2971_, size_t v_sz_2972_, size_t v_i_2973_, lean_object* v_b_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
lean_object* v___x_2978_; 
v___x_2978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_2971_, v_sz_2972_, v_i_2973_, v_b_2974_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___boxed(lean_object* v_as_2979_, lean_object* v_sz_2980_, lean_object* v_i_2981_, lean_object* v_b_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
size_t v_sz_boxed_2986_; size_t v_i_boxed_2987_; lean_object* v_res_2988_; 
v_sz_boxed_2986_ = lean_unbox_usize(v_sz_2980_);
lean_dec(v_sz_2980_);
v_i_boxed_2987_ = lean_unbox_usize(v_i_2981_);
lean_dec(v_i_2981_);
v_res_2988_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(v_as_2979_, v_sz_boxed_2986_, v_i_boxed_2987_, v_b_2982_, v___y_2983_, v___y_2984_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
lean_dec_ref(v_as_2979_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object* v_init_2989_, lean_object* v_t_2990_){
_start:
{
lean_object* v___x_2991_; 
v___x_2991_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_2989_, v_t_2990_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object* v_init_2992_, lean_object* v_t_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(v_init_2992_, v_t_2993_);
lean_dec(v_t_2993_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object* v_n_2995_, lean_object* v_as_2996_, lean_object* v_lo_2997_, lean_object* v_hi_2998_, lean_object* v_w_2999_, lean_object* v_hlo_3000_, lean_object* v_hhi_3001_){
_start:
{
lean_object* v___x_3002_; 
v___x_3002_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_2995_, v_as_2996_, v_lo_2997_, v_hi_2998_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object* v_n_3003_, lean_object* v_as_3004_, lean_object* v_lo_3005_, lean_object* v_hi_3006_, lean_object* v_w_3007_, lean_object* v_hlo_3008_, lean_object* v_hhi_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(v_n_3003_, v_as_3004_, v_lo_3005_, v_hi_3006_, v_w_3007_, v_hlo_3008_, v_hhi_3009_);
lean_dec(v_hi_3006_);
lean_dec(v_n_3003_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object* v_init_3011_, lean_object* v_x_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
lean_object* v___x_3016_; 
v___x_3016_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_3011_, v_x_3012_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object* v_init_3017_, lean_object* v_x_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(v_init_3017_, v_x_3018_, v___y_3019_, v___y_3020_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_3023_, lean_object* v_x_3024_, size_t v_x_3025_, lean_object* v_x_3026_){
_start:
{
lean_object* v___x_3027_; 
v___x_3027_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3024_, v_x_3025_, v_x_3026_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3028_, lean_object* v_x_3029_, lean_object* v_x_3030_, lean_object* v_x_3031_){
_start:
{
size_t v_x_18950__boxed_3032_; lean_object* v_res_3033_; 
v_x_18950__boxed_3032_ = lean_unbox_usize(v_x_3030_);
lean_dec(v_x_3030_);
v_res_3033_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(v_00_u03b2_3028_, v_x_3029_, v_x_18950__boxed_3032_, v_x_3031_);
lean_dec(v_x_3031_);
lean_dec_ref(v_x_3029_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object* v_as_3034_, lean_object* v_k_3035_, lean_object* v_x_3036_, lean_object* v_x_3037_, lean_object* v_x_3038_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_3034_, v_k_3035_, v_x_3036_, v_x_3037_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object* v_as_3040_, lean_object* v_k_3041_, lean_object* v_x_3042_, lean_object* v_x_3043_, lean_object* v_x_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(v_as_3040_, v_k_3041_, v_x_3042_, v_x_3043_, v_x_3044_);
lean_dec_ref(v_k_3041_);
lean_dec_ref(v_as_3040_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(lean_object* v_00_u03b2_3046_, lean_object* v_m_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v___x_3049_; 
v___x_3049_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_3047_, v_a_3048_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___boxed(lean_object* v_00_u03b2_3050_, lean_object* v_m_3051_, lean_object* v_a_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(v_00_u03b2_3050_, v_m_3051_, v_a_3052_);
lean_dec(v_a_3052_);
lean_dec_ref(v_m_3051_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(lean_object* v_n_3054_, lean_object* v_lo_3055_, lean_object* v_hi_3056_, lean_object* v_hhi_3057_, lean_object* v_pivot_3058_, lean_object* v_as_3059_, lean_object* v_i_3060_, lean_object* v_k_3061_, lean_object* v_ilo_3062_, lean_object* v_ik_3063_, lean_object* v_w_3064_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_3056_, v_pivot_3058_, v_as_3059_, v_i_3060_, v_k_3061_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___boxed(lean_object* v_n_3066_, lean_object* v_lo_3067_, lean_object* v_hi_3068_, lean_object* v_hhi_3069_, lean_object* v_pivot_3070_, lean_object* v_as_3071_, lean_object* v_i_3072_, lean_object* v_k_3073_, lean_object* v_ilo_3074_, lean_object* v_ik_3075_, lean_object* v_w_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(v_n_3066_, v_lo_3067_, v_hi_3068_, v_hhi_3069_, v_pivot_3070_, v_as_3071_, v_i_3072_, v_k_3073_, v_ilo_3074_, v_ik_3075_, v_w_3076_);
lean_dec(v_hi_3068_);
lean_dec(v_lo_3067_);
lean_dec(v_n_3066_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_3078_, lean_object* v_keys_3079_, lean_object* v_vals_3080_, lean_object* v_heq_3081_, lean_object* v_i_3082_, lean_object* v_k_3083_){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_3079_, v_vals_3080_, v_i_3082_, v_k_3083_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object* v_00_u03b2_3085_, lean_object* v_keys_3086_, lean_object* v_vals_3087_, lean_object* v_heq_3088_, lean_object* v_i_3089_, lean_object* v_k_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(v_00_u03b2_3085_, v_keys_3086_, v_vals_3087_, v_heq_3088_, v_i_3089_, v_k_3090_);
lean_dec(v_k_3090_);
lean_dec_ref(v_vals_3087_);
lean_dec_ref(v_keys_3086_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(lean_object* v_00_u03b2_3092_, lean_object* v_a_3093_, lean_object* v_x_3094_){
_start:
{
lean_object* v___x_3095_; 
v___x_3095_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_3093_, v_x_3094_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___boxed(lean_object* v_00_u03b2_3096_, lean_object* v_a_3097_, lean_object* v_x_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(v_00_u03b2_3096_, v_a_3097_, v_x_3098_);
lean_dec(v_x_3098_);
lean_dec(v_a_3097_);
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1(){
_start:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3114_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3115_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1));
v___x_3116_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3117_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed), 4, 0);
v___x_3118_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3114_, v___x_3115_, v___x_3116_, v___x_3117_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object* v_a_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3(){
_start:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3123_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3124_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0));
v___x_3125_ = l_Lean_addBuiltinDocString(v___x_3123_, v___x_3124_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object* v_a_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5(){
_start:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3154_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3155_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6));
v___x_3156_ = l_Lean_addBuiltinDeclarationRanges(v___x_3154_, v___x_3155_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object* v_a_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object* v_env_3159_, lean_object* v___x_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, uint8_t v_includeUnnamed_3163_, lean_object* v_x_3164_, lean_object* v_____s_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v_fst_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3226_; 
v_fst_3171_ = lean_ctor_get(v_x_3164_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v_x_3164_);
if (v_isSharedCheck_3226_ == 0)
{
lean_object* v_unused_3227_; 
v_unused_3227_ = lean_ctor_get(v_x_3164_, 1);
lean_dec(v_unused_3227_);
v___x_3173_ = v_x_3164_;
v_isShared_3174_ = v_isSharedCheck_3226_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_fst_3171_);
lean_dec(v_x_3164_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3226_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v_userName_3176_; lean_object* v___y_3177_; lean_object* v___x_3211_; 
lean_inc(v_fst_3171_);
lean_inc_ref(v_env_3159_);
v___x_3211_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_3159_, v_fst_3171_);
if (lean_obj_tag(v___x_3211_) == 1)
{
lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3219_; 
lean_del_object(v___x_3173_);
lean_dec(v_fst_3171_);
lean_dec(v___x_3160_);
lean_dec_ref(v_env_3159_);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3219_ == 0)
{
lean_object* v_unused_3220_; 
v_unused_3220_ = lean_ctor_get(v___x_3211_, 0);
lean_dec(v_unused_3220_);
v___x_3213_ = v___x_3211_;
v_isShared_3214_ = v_isSharedCheck_3219_;
goto v_resetjp_3212_;
}
else
{
lean_dec(v___x_3211_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3219_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
lean_ctor_set(v___x_3213_, 0, v_____s_3165_);
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_____s_3165_);
v___x_3216_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
lean_object* v___x_3217_; 
v___x_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
return v___x_3217_;
}
}
}
else
{
lean_object* v___x_3221_; 
lean_dec(v___x_3211_);
v___x_3221_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_a_3162_, v_fst_3171_);
if (lean_obj_tag(v___x_3221_) == 1)
{
lean_object* v_val_3222_; 
v_val_3222_ = lean_ctor_get(v___x_3221_, 0);
lean_inc(v_val_3222_);
lean_dec_ref_known(v___x_3221_, 1);
v_userName_3176_ = v_val_3222_;
v___y_3177_ = v___y_3168_;
goto v___jp_3175_;
}
else
{
lean_dec(v___x_3221_);
if (v_includeUnnamed_3163_ == 0)
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
lean_del_object(v___x_3173_);
lean_dec(v_fst_3171_);
lean_dec(v___x_3160_);
lean_dec_ref(v_env_3159_);
v___x_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3223_, 0, v_____s_3165_);
v___x_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
return v___x_3224_;
}
else
{
lean_object* v___x_3225_; 
lean_inc(v_fst_3171_);
v___x_3225_ = l_Lean_Name_toString(v_fst_3171_, v_includeUnnamed_3163_);
v_userName_3176_ = v___x_3225_;
v___y_3177_ = v___y_3168_;
goto v___jp_3175_;
}
}
}
v___jp_3175_:
{
uint8_t v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3178_ = 1;
v___x_3179_ = l_Lean_Options_empty;
v___x_3180_ = lean_box(0);
lean_inc(v_fst_3171_);
lean_inc_ref(v_env_3159_);
v___x_3181_ = l_Lean_findDocString_x3f(v_env_3159_, v_fst_3171_, v___x_3178_, v___x_3179_, v___x_3160_, v___x_3180_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3195_; 
lean_del_object(v___x_3173_);
v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3184_ = v___x_3181_;
v_isShared_3185_ = v_isSharedCheck_3195_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3181_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3195_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3193_; 
v___x_3186_ = l_Lean_NameSet_empty;
v___x_3187_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_a_3161_, v_fst_3171_, v___x_3186_);
lean_inc(v_fst_3171_);
v___x_3188_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_3159_, v_fst_3171_);
v___x_3189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3189_, 0, v_fst_3171_);
lean_ctor_set(v___x_3189_, 1, v_userName_3176_);
lean_ctor_set(v___x_3189_, 2, v___x_3187_);
lean_ctor_set(v___x_3189_, 3, v_a_3182_);
lean_ctor_set(v___x_3189_, 4, v___x_3188_);
v___x_3190_ = lean_array_push(v_____s_3165_, v___x_3189_);
v___x_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 0, v___x_3191_);
v___x_3193_ = v___x_3184_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3191_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
else
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3210_; 
lean_dec_ref(v_userName_3176_);
lean_dec(v_fst_3171_);
lean_dec_ref(v_____s_3165_);
lean_dec_ref(v_env_3159_);
v_a_3196_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3198_ = v___x_3181_;
v_isShared_3199_ = v_isSharedCheck_3210_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3181_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3210_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v_ref_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3205_; 
v_ref_3200_ = lean_ctor_get(v___y_3177_, 4);
v___x_3201_ = lean_io_error_to_string(v_a_3196_);
v___x_3202_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3201_);
v___x_3203_ = l_Lean_MessageData_ofFormat(v___x_3202_);
lean_inc(v_ref_3200_);
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 1, v___x_3203_);
lean_ctor_set(v___x_3173_, 0, v_ref_3200_);
v___x_3205_ = v___x_3173_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_ref_3200_);
lean_ctor_set(v_reuseFailAlloc_3209_, 1, v___x_3203_);
v___x_3205_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
lean_object* v___x_3207_; 
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 0, v___x_3205_);
v___x_3207_ = v___x_3198_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3205_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object* v_env_3228_, lean_object* v___x_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_includeUnnamed_3232_, lean_object* v_x_3233_, lean_object* v_____s_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_){
_start:
{
uint8_t v_includeUnnamed_boxed_3240_; lean_object* v_res_3241_; 
v_includeUnnamed_boxed_3240_ = lean_unbox(v_includeUnnamed_3232_);
v_res_3241_ = l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(v_env_3228_, v___x_3229_, v_a_3230_, v_a_3231_, v_includeUnnamed_boxed_3240_, v_x_3233_, v_____s_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v_a_3231_);
lean_dec(v_a_3230_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object* v_as_3242_, size_t v_sz_3243_, size_t v_i_3244_, lean_object* v_b_3245_){
_start:
{
uint8_t v___x_3247_; 
v___x_3247_ = lean_usize_dec_lt(v_i_3244_, v_sz_3243_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3248_; 
v___x_3248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3248_, 0, v_b_3245_);
return v___x_3248_;
}
else
{
lean_object* v_a_3249_; lean_object* v_fst_3250_; lean_object* v_snd_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; size_t v___x_3256_; size_t v___x_3257_; 
v_a_3249_ = lean_array_uget_borrowed(v_as_3242_, v_i_3244_);
v_fst_3250_ = lean_ctor_get(v_a_3249_, 0);
v_snd_3251_ = lean_ctor_get(v_a_3249_, 1);
v___x_3252_ = l_Lean_NameSet_empty;
v___x_3253_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_3245_, v_fst_3250_, v___x_3252_);
lean_inc(v_snd_3251_);
v___x_3254_ = l_Lean_NameSet_insert(v___x_3253_, v_snd_3251_);
lean_inc(v_fst_3250_);
v___x_3255_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3250_, v___x_3254_, v_b_3245_);
v___x_3256_ = ((size_t)1ULL);
v___x_3257_ = lean_usize_add(v_i_3244_, v___x_3256_);
v_i_3244_ = v___x_3257_;
v_b_3245_ = v___x_3255_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object* v_as_3259_, lean_object* v_sz_3260_, lean_object* v_i_3261_, lean_object* v_b_3262_, lean_object* v___y_3263_){
_start:
{
size_t v_sz_boxed_3264_; size_t v_i_boxed_3265_; lean_object* v_res_3266_; 
v_sz_boxed_3264_ = lean_unbox_usize(v_sz_3260_);
lean_dec(v_sz_3260_);
v_i_boxed_3265_ = lean_unbox_usize(v_i_3261_);
lean_dec(v_i_3261_);
v_res_3266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_3259_, v_sz_boxed_3264_, v_i_boxed_3265_, v_b_3262_);
lean_dec_ref(v_as_3259_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object* v_as_3267_, size_t v_sz_3268_, size_t v_i_3269_, lean_object* v_b_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
uint8_t v___x_3276_; 
v___x_3276_ = lean_usize_dec_lt(v_i_3269_, v_sz_3268_);
if (v___x_3276_ == 0)
{
lean_object* v___x_3277_; 
v___x_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3277_, 0, v_b_3270_);
return v___x_3277_;
}
else
{
lean_object* v_a_3278_; size_t v_sz_3279_; size_t v___x_3280_; lean_object* v___x_3281_; 
v_a_3278_ = lean_array_uget_borrowed(v_as_3267_, v_i_3269_);
v_sz_3279_ = lean_array_size(v_a_3278_);
v___x_3280_ = ((size_t)0ULL);
v___x_3281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_a_3278_, v_sz_3279_, v___x_3280_, v_b_3270_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v_a_3282_; size_t v___x_3283_; size_t v___x_3284_; 
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_a_3282_);
lean_dec_ref_known(v___x_3281_, 1);
v___x_3283_ = ((size_t)1ULL);
v___x_3284_ = lean_usize_add(v_i_3269_, v___x_3283_);
v_i_3269_ = v___x_3284_;
v_b_3270_ = v_a_3282_;
goto _start;
}
else
{
return v___x_3281_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object* v_as_3286_, lean_object* v_sz_3287_, lean_object* v_i_3288_, lean_object* v_b_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
size_t v_sz_boxed_3295_; size_t v_i_boxed_3296_; lean_object* v_res_3297_; 
v_sz_boxed_3295_ = lean_unbox_usize(v_sz_3287_);
lean_dec(v_sz_3287_);
v_i_boxed_3296_ = lean_unbox_usize(v_i_3288_);
lean_dec(v_i_3288_);
v_res_3297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v_as_3286_, v_sz_boxed_3295_, v_i_boxed_3296_, v_b_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec_ref(v_as_3286_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object* v_f_3298_, lean_object* v_keys_3299_, lean_object* v_vals_3300_, lean_object* v_i_3301_, lean_object* v_acc_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
lean_object* v___x_3308_; uint8_t v___x_3309_; 
v___x_3308_ = lean_array_get_size(v_keys_3299_);
v___x_3309_ = lean_nat_dec_lt(v_i_3301_, v___x_3308_);
if (v___x_3309_ == 0)
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
lean_dec(v_i_3301_);
lean_dec_ref(v_f_3298_);
v___x_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3310_, 0, v_acc_3302_);
v___x_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
return v___x_3311_;
}
else
{
lean_object* v_k_3312_; lean_object* v_v_3313_; lean_object* v___x_3314_; 
v_k_3312_ = lean_array_fget_borrowed(v_keys_3299_, v_i_3301_);
v_v_3313_ = lean_array_fget_borrowed(v_vals_3300_, v_i_3301_);
lean_inc_ref(v_f_3298_);
lean_inc(v___y_3306_);
lean_inc_ref(v___y_3305_);
lean_inc(v___y_3304_);
lean_inc_ref(v___y_3303_);
lean_inc(v_v_3313_);
lean_inc(v_k_3312_);
v___x_3314_ = lean_apply_8(v_f_3298_, v_acc_3302_, v_k_3312_, v_v_3313_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, lean_box(0));
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v_a_3315_; 
v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_a_3315_);
if (lean_obj_tag(v_a_3315_) == 0)
{
lean_dec_ref_known(v_a_3315_, 1);
lean_dec(v_i_3301_);
lean_dec_ref(v_f_3298_);
return v___x_3314_;
}
else
{
lean_object* v_a_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
lean_dec_ref_known(v___x_3314_, 1);
v_a_3316_ = lean_ctor_get(v_a_3315_, 0);
lean_inc(v_a_3316_);
lean_dec_ref_known(v_a_3315_, 1);
v___x_3317_ = lean_unsigned_to_nat(1u);
v___x_3318_ = lean_nat_add(v_i_3301_, v___x_3317_);
lean_dec(v_i_3301_);
v_i_3301_ = v___x_3318_;
v_acc_3302_ = v_a_3316_;
goto _start;
}
}
else
{
lean_dec(v_i_3301_);
lean_dec_ref(v_f_3298_);
return v___x_3314_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_f_3320_, lean_object* v_keys_3321_, lean_object* v_vals_3322_, lean_object* v_i_3323_, lean_object* v_acc_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3320_, v_keys_3321_, v_vals_3322_, v_i_3323_, v_acc_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
lean_dec(v___y_3326_);
lean_dec_ref(v___y_3325_);
lean_dec_ref(v_vals_3322_);
lean_dec_ref(v_keys_3321_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_f_3331_, lean_object* v_as_3332_, size_t v_i_3333_, size_t v_stop_3334_, lean_object* v_b_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v_a_3342_; lean_object* v___y_3347_; uint8_t v___x_3350_; 
v___x_3350_ = lean_usize_dec_eq(v_i_3333_, v_stop_3334_);
if (v___x_3350_ == 0)
{
lean_object* v___x_3351_; 
v___x_3351_ = lean_array_uget_borrowed(v_as_3332_, v_i_3333_);
switch(lean_obj_tag(v___x_3351_))
{
case 0:
{
lean_object* v_key_3352_; lean_object* v_val_3353_; lean_object* v___x_3354_; 
v_key_3352_ = lean_ctor_get(v___x_3351_, 0);
v_val_3353_ = lean_ctor_get(v___x_3351_, 1);
lean_inc_ref(v_f_3331_);
lean_inc(v___y_3339_);
lean_inc_ref(v___y_3338_);
lean_inc(v___y_3337_);
lean_inc_ref(v___y_3336_);
lean_inc(v_val_3353_);
lean_inc(v_key_3352_);
v___x_3354_ = lean_apply_8(v_f_3331_, v_b_3335_, v_key_3352_, v_val_3353_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, lean_box(0));
v___y_3347_ = v___x_3354_;
goto v___jp_3346_;
}
case 1:
{
lean_object* v_node_3355_; lean_object* v___x_3356_; 
v_node_3355_ = lean_ctor_get(v___x_3351_, 0);
lean_inc(v_node_3355_);
lean_inc_ref(v_f_3331_);
v___x_3356_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3331_, v_node_3355_, v_b_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
v___y_3347_ = v___x_3356_;
goto v___jp_3346_;
}
default: 
{
v_a_3342_ = v_b_3335_;
goto v___jp_3341_;
}
}
}
else
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
lean_dec_ref(v_f_3331_);
v___x_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3357_, 0, v_b_3335_);
v___x_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
return v___x_3358_;
}
v___jp_3341_:
{
size_t v___x_3343_; size_t v___x_3344_; 
v___x_3343_ = ((size_t)1ULL);
v___x_3344_ = lean_usize_add(v_i_3333_, v___x_3343_);
v_i_3333_ = v___x_3344_;
v_b_3335_ = v_a_3342_;
goto _start;
}
v___jp_3346_:
{
if (lean_obj_tag(v___y_3347_) == 0)
{
lean_object* v_a_3348_; 
v_a_3348_ = lean_ctor_get(v___y_3347_, 0);
if (lean_obj_tag(v_a_3348_) == 0)
{
lean_dec_ref(v_f_3331_);
return v___y_3347_;
}
else
{
lean_object* v_a_3349_; 
lean_inc_ref(v_a_3348_);
lean_dec_ref_known(v___y_3347_, 1);
v_a_3349_ = lean_ctor_get(v_a_3348_, 0);
lean_inc(v_a_3349_);
lean_dec_ref_known(v_a_3348_, 1);
v_a_3342_ = v_a_3349_;
goto v___jp_3341_;
}
}
else
{
lean_dec_ref(v_f_3331_);
return v___y_3347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object* v_f_3359_, lean_object* v_x_3360_, lean_object* v_x_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
if (lean_obj_tag(v_x_3360_) == 0)
{
lean_object* v_es_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3381_; 
v_es_3367_ = lean_ctor_get(v_x_3360_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v_x_3360_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3369_ = v_x_3360_;
v_isShared_3370_ = v_isSharedCheck_3381_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_es_3367_);
lean_dec(v_x_3360_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3381_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; 
v___x_3371_ = lean_unsigned_to_nat(0u);
v___x_3372_ = lean_array_get_size(v_es_3367_);
v___x_3373_ = lean_nat_dec_lt(v___x_3371_, v___x_3372_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3375_; 
lean_dec_ref(v_es_3367_);
lean_dec_ref(v_f_3359_);
if (v_isShared_3370_ == 0)
{
lean_ctor_set_tag(v___x_3369_, 1);
lean_ctor_set(v___x_3369_, 0, v_x_3361_);
v___x_3375_ = v___x_3369_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_x_3361_);
v___x_3375_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3376_; 
v___x_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3375_);
return v___x_3376_;
}
}
else
{
size_t v___x_3378_; size_t v___x_3379_; lean_object* v___x_3380_; 
lean_del_object(v___x_3369_);
v___x_3378_ = ((size_t)0ULL);
v___x_3379_ = lean_usize_of_nat(v___x_3372_);
v___x_3380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3359_, v_es_3367_, v___x_3378_, v___x_3379_, v_x_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
lean_dec_ref(v_es_3367_);
return v___x_3380_;
}
}
}
else
{
lean_object* v_ks_3382_; lean_object* v_vs_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v_ks_3382_ = lean_ctor_get(v_x_3360_, 0);
lean_inc_ref(v_ks_3382_);
v_vs_3383_ = lean_ctor_get(v_x_3360_, 1);
lean_inc_ref(v_vs_3383_);
lean_dec_ref_known(v_x_3360_, 2);
v___x_3384_ = lean_unsigned_to_nat(0u);
v___x_3385_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3359_, v_ks_3382_, v_vs_3383_, v___x_3384_, v_x_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
lean_dec_ref(v_vs_3383_);
lean_dec_ref(v_ks_3382_);
return v___x_3385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_f_3386_, lean_object* v_x_3387_, lean_object* v_x_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3386_, v_x_3387_, v_x_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_3395_, lean_object* v_as_3396_, lean_object* v_i_3397_, lean_object* v_stop_3398_, lean_object* v_b_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
size_t v_i_boxed_3405_; size_t v_stop_boxed_3406_; lean_object* v_res_3407_; 
v_i_boxed_3405_ = lean_unbox_usize(v_i_3397_);
lean_dec(v_i_3397_);
v_stop_boxed_3406_ = lean_unbox_usize(v_stop_3398_);
lean_dec(v_stop_3398_);
v_res_3407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3395_, v_as_3396_, v_i_boxed_3405_, v_stop_boxed_3406_, v_b_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec_ref(v_as_3396_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object* v_f_3408_, lean_object* v_s_3409_, lean_object* v_a_3410_, lean_object* v_b_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3417_, 0, v_a_3410_);
lean_ctor_set(v___x_3417_, 1, v_b_3411_);
lean_inc(v___y_3415_);
lean_inc_ref(v___y_3414_);
lean_inc(v___y_3413_);
lean_inc_ref(v___y_3412_);
v___x_3418_ = lean_apply_7(v_f_3408_, v___x_3417_, v_s_3409_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, lean_box(0));
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3445_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3421_ = v___x_3418_;
v_isShared_3422_ = v_isSharedCheck_3445_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3418_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3445_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
if (lean_obj_tag(v_a_3419_) == 0)
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3433_; 
v_a_3423_ = lean_ctor_get(v_a_3419_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v_a_3419_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3425_ = v_a_3419_;
v_isShared_3426_ = v_isSharedCheck_3433_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v_a_3419_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3433_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
lean_object* v___x_3430_; 
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 0, v___x_3428_);
v___x_3430_ = v___x_3421_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3428_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3444_; 
v_a_3434_ = lean_ctor_get(v_a_3419_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v_a_3419_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3436_ = v_a_3419_;
v_isShared_3437_ = v_isSharedCheck_3444_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v_a_3419_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3444_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
lean_object* v___x_3441_; 
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 0, v___x_3439_);
v___x_3441_ = v___x_3421_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___x_3439_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
}
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
v_a_3446_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v___x_3418_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3418_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3446_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object* v_f_3454_, lean_object* v_s_3455_, lean_object* v_a_3456_, lean_object* v_b_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
lean_object* v_res_3463_; 
v_res_3463_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(v_f_3454_, v_s_3455_, v_a_3456_, v_b_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object* v_map_3464_, lean_object* v_init_3465_, lean_object* v_f_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v___f_3472_; lean_object* v___x_3473_; 
v___f_3472_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3472_, 0, v_f_3466_);
lean_inc_ref(v_map_3464_);
v___x_3473_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v___f_3472_, v_map_3464_, v_init_3465_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3482_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3476_ = v___x_3473_;
v_isShared_3477_ = v_isSharedCheck_3482_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3473_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3482_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v_a_3478_; lean_object* v___x_3480_; 
v_a_3478_ = lean_ctor_get(v_a_3474_, 0);
lean_inc(v_a_3478_);
lean_dec(v_a_3474_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 0, v_a_3478_);
v___x_3480_ = v___x_3476_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3478_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
v_a_3483_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3473_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3473_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object* v_map_3491_, lean_object* v_init_3492_, lean_object* v_f_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_){
_start:
{
lean_object* v_res_3499_; 
v_res_3499_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_3491_, v_init_3492_, v_f_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec_ref(v_map_3491_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object* v___y_3500_){
_start:
{
lean_object* v___x_3502_; lean_object* v_env_3503_; lean_object* v___x_3504_; lean_object* v_ext_3505_; lean_object* v_toEnvExtension_3506_; lean_object* v_asyncMode_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v_categories_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3502_ = lean_st_ref_get(v___y_3500_);
v_env_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc_ref_n(v_env_3503_, 2);
lean_dec(v___x_3502_);
v___x_3504_ = l_Lean_Parser_parserExtension;
v_ext_3505_ = lean_ctor_get(v___x_3504_, 1);
v_toEnvExtension_3506_ = lean_ctor_get(v_ext_3505_, 0);
v_asyncMode_3507_ = lean_ctor_get(v_toEnvExtension_3506_, 2);
v___x_3508_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3509_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3508_, v___x_3504_, v_env_3503_, v_asyncMode_3507_);
v_categories_3510_ = lean_ctor_get(v___x_3509_, 2);
lean_inc_ref(v_categories_3510_);
lean_dec(v___x_3509_);
v___x_3511_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3512_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3510_, v___x_3511_);
lean_dec_ref(v_categories_3510_);
if (lean_obj_tag(v___x_3512_) == 1)
{
lean_object* v_val_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3546_; 
v_val_3513_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3515_ = v___x_3512_;
v_isShared_3516_ = v_isSharedCheck_3546_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_val_3513_);
lean_dec(v___x_3512_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3546_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___y_3518_; lean_object* v___x_3527_; lean_object* v_toEnvExtension_3528_; lean_object* v_exportEntriesFn_3529_; lean_object* v_asyncMode_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v_importedEntries_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v_exported_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; uint8_t v___x_3542_; 
v___x_3527_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3528_ = lean_ctor_get(v___x_3527_, 0);
v_exportEntriesFn_3529_ = lean_ctor_get(v___x_3527_, 4);
v_asyncMode_3530_ = lean_ctor_get(v_toEnvExtension_3528_, 2);
v___x_3531_ = lean_box(1);
v___x_3532_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3533_ = lean_box(0);
lean_inc_ref_n(v_env_3503_, 2);
v___x_3534_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3532_, v_toEnvExtension_3528_, v_env_3503_, v_asyncMode_3530_, v___x_3533_);
v_importedEntries_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc_ref(v_importedEntries_3535_);
lean_dec(v___x_3534_);
v___x_3536_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3531_, v___x_3527_, v_env_3503_, v_asyncMode_3530_, v___x_3533_);
lean_inc_ref(v_exportEntriesFn_3529_);
v___x_3537_ = lean_apply_2(v_exportEntriesFn_3529_, v_env_3503_, v___x_3536_);
v_exported_3538_ = lean_ctor_get(v___x_3537_, 0);
lean_inc(v_exported_3538_);
lean_dec_ref(v___x_3537_);
v___x_3539_ = lean_array_push(v_importedEntries_3535_, v_exported_3538_);
v___x_3540_ = lean_unsigned_to_nat(0u);
v___x_3541_ = lean_array_get_size(v___x_3539_);
v___x_3542_ = lean_nat_dec_lt(v___x_3540_, v___x_3541_);
if (v___x_3542_ == 0)
{
lean_dec_ref(v___x_3539_);
v___y_3518_ = v___x_3531_;
goto v___jp_3517_;
}
else
{
size_t v___x_3543_; size_t v___x_3544_; lean_object* v___x_3545_; 
v___x_3543_ = ((size_t)0ULL);
v___x_3544_ = lean_usize_of_nat(v___x_3541_);
v___x_3545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3539_, v___x_3543_, v___x_3544_, v___x_3531_);
lean_dec_ref(v___x_3539_);
v___y_3518_ = v___x_3545_;
goto v___jp_3517_;
}
v___jp_3517_:
{
lean_object* v_tables_3519_; lean_object* v_leadingTable_3520_; lean_object* v_trailingTable_3521_; lean_object* v_firstTokens_3522_; lean_object* v_firstTokens_3523_; lean_object* v___x_3525_; 
v_tables_3519_ = lean_ctor_get(v_val_3513_, 2);
v_leadingTable_3520_ = lean_ctor_get(v_tables_3519_, 0);
v_trailingTable_3521_ = lean_ctor_get(v_tables_3519_, 2);
lean_inc(v_trailingTable_3521_);
lean_inc(v_leadingTable_3520_);
lean_inc(v_val_3513_);
v_firstTokens_3522_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3513_, v_leadingTable_3520_, v___y_3518_);
v_firstTokens_3523_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3513_, v_trailingTable_3521_, v_firstTokens_3522_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set_tag(v___x_3515_, 0);
lean_ctor_set(v___x_3515_, 0, v_firstTokens_3523_);
v___x_3525_ = v___x_3515_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_firstTokens_3523_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
else
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
lean_dec(v___x_3512_);
lean_dec_ref(v_env_3503_);
v___x_3547_ = lean_box(1);
v___x_3548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3547_);
return v___x_3548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
lean_object* v_res_3551_; 
v_res_3551_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_3549_);
lean_dec(v___y_3549_);
return v_res_3551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t v_includeUnnamed_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_){
_start:
{
lean_object* v___x_3560_; lean_object* v_env_3561_; lean_object* v___x_3562_; lean_object* v_toEnvExtension_3563_; lean_object* v_exportEntriesFn_3564_; lean_object* v_asyncMode_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v_importedEntries_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v_exported_3573_; lean_object* v___x_3574_; size_t v_sz_3575_; size_t v___x_3576_; lean_object* v___x_3577_; 
v___x_3560_ = lean_st_ref_get(v_a_3558_);
v_env_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc_ref_n(v_env_3561_, 4);
lean_dec(v___x_3560_);
v___x_3562_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_3563_ = lean_ctor_get(v___x_3562_, 0);
v_exportEntriesFn_3564_ = lean_ctor_get(v___x_3562_, 4);
v_asyncMode_3565_ = lean_ctor_get(v_toEnvExtension_3563_, 2);
v___x_3566_ = lean_box(1);
v___x_3567_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_3568_ = lean_box(0);
v___x_3569_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3567_, v_toEnvExtension_3563_, v_env_3561_, v_asyncMode_3565_, v___x_3568_);
v_importedEntries_3570_ = lean_ctor_get(v___x_3569_, 0);
lean_inc_ref(v_importedEntries_3570_);
lean_dec(v___x_3569_);
v___x_3571_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3566_, v___x_3562_, v_env_3561_, v_asyncMode_3565_, v___x_3568_);
lean_inc_ref(v_exportEntriesFn_3564_);
v___x_3572_ = lean_apply_2(v_exportEntriesFn_3564_, v_env_3561_, v___x_3571_);
v_exported_3573_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_exported_3573_);
lean_dec_ref(v___x_3572_);
v___x_3574_ = lean_array_push(v_importedEntries_3570_, v_exported_3573_);
v_sz_3575_ = lean_array_size(v___x_3574_);
v___x_3576_ = ((size_t)0ULL);
v___x_3577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v___x_3574_, v_sz_3575_, v___x_3576_, v___x_3566_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
lean_dec_ref(v___x_3574_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3602_; 
v_a_3578_ = lean_ctor_get(v___x_3577_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3580_ = v___x_3577_;
v_isShared_3581_ = v_isSharedCheck_3602_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3577_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3602_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3582_; lean_object* v_ext_3583_; lean_object* v_toEnvExtension_3584_; lean_object* v_asyncMode_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v_categories_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3582_ = l_Lean_Parser_parserExtension;
v_ext_3583_ = lean_ctor_get(v___x_3582_, 1);
v_toEnvExtension_3584_ = lean_ctor_get(v_ext_3583_, 0);
v_asyncMode_3585_ = lean_ctor_get(v_toEnvExtension_3584_, 2);
v___x_3586_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref(v_env_3561_);
v___x_3587_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3586_, v___x_3582_, v_env_3561_, v_asyncMode_3585_);
v_categories_3588_ = lean_ctor_get(v___x_3587_, 2);
lean_inc_ref(v_categories_3588_);
lean_dec(v___x_3587_);
v___x_3589_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0));
v___x_3590_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3591_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3588_, v___x_3590_);
lean_dec_ref(v_categories_3588_);
if (lean_obj_tag(v___x_3591_) == 1)
{
lean_object* v_val_3592_; lean_object* v___x_3593_; lean_object* v_a_3594_; lean_object* v_kinds_3595_; lean_object* v___x_3596_; lean_object* v___f_3597_; lean_object* v___x_3598_; 
lean_del_object(v___x_3580_);
v_val_3592_ = lean_ctor_get(v___x_3591_, 0);
lean_inc(v_val_3592_);
lean_dec_ref_known(v___x_3591_, 1);
v___x_3593_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v_a_3558_);
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_a_3594_);
lean_dec_ref(v___x_3593_);
v_kinds_3595_ = lean_ctor_get(v_val_3592_, 1);
lean_inc_ref(v_kinds_3595_);
lean_dec(v_val_3592_);
v___x_3596_ = lean_box(v_includeUnnamed_3554_);
v___f_3597_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed), 12, 5);
lean_closure_set(v___f_3597_, 0, v_env_3561_);
lean_closure_set(v___f_3597_, 1, v___x_3568_);
lean_closure_set(v___f_3597_, 2, v_a_3578_);
lean_closure_set(v___f_3597_, 3, v_a_3594_);
lean_closure_set(v___f_3597_, 4, v___x_3596_);
v___x_3598_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_kinds_3595_, v___x_3589_, v___f_3597_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
lean_dec_ref(v_kinds_3595_);
return v___x_3598_;
}
else
{
lean_object* v___x_3600_; 
lean_dec(v___x_3591_);
lean_dec(v_a_3578_);
lean_dec_ref(v_env_3561_);
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 0, v___x_3589_);
v___x_3600_ = v___x_3580_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3589_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
else
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
lean_dec_ref(v_env_3561_);
v_a_3603_ = lean_ctor_get(v___x_3577_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3605_ = v___x_3577_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3577_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3603_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object* v_includeUnnamed_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_){
_start:
{
uint8_t v_includeUnnamed_boxed_3617_; lean_object* v_res_3618_; 
v_includeUnnamed_boxed_3617_ = lean_unbox(v_includeUnnamed_3611_);
v_res_3618_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v_includeUnnamed_boxed_3617_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_);
lean_dec(v_a_3615_);
lean_dec_ref(v_a_3614_);
lean_dec(v_a_3613_);
lean_dec_ref(v_a_3612_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object* v_as_3619_, size_t v_sz_3620_, size_t v_i_3621_, lean_object* v_b_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_){
_start:
{
lean_object* v___x_3628_; 
v___x_3628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_3619_, v_sz_3620_, v_i_3621_, v_b_3622_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object* v_as_3629_, lean_object* v_sz_3630_, lean_object* v_i_3631_, lean_object* v_b_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
size_t v_sz_boxed_3638_; size_t v_i_boxed_3639_; lean_object* v_res_3640_; 
v_sz_boxed_3638_ = lean_unbox_usize(v_sz_3630_);
lean_dec(v_sz_3630_);
v_i_boxed_3639_ = lean_unbox_usize(v_i_3631_);
lean_dec(v_i_3631_);
v_res_3640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(v_as_3629_, v_sz_boxed_3638_, v_i_boxed_3639_, v_b_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec_ref(v_as_3629_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v___x_3646_; 
v___x_3646_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_3644_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object* v_00_u03c3_3653_, lean_object* v_00_u03b2_3654_, lean_object* v_map_3655_, lean_object* v_init_3656_, lean_object* v_f_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_){
_start:
{
lean_object* v___x_3663_; 
v___x_3663_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_3655_, v_init_3656_, v_f_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object* v_00_u03c3_3664_, lean_object* v_00_u03b2_3665_, lean_object* v_map_3666_, lean_object* v_init_3667_, lean_object* v_f_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(v_00_u03c3_3664_, v_00_u03b2_3665_, v_map_3666_, v_init_3667_, v_f_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec_ref(v_map_3666_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object* v_map_3675_, lean_object* v_f_3676_, lean_object* v_init_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
lean_object* v___x_3683_; 
v___x_3683_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3676_, v_map_3675_, v_init_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object* v_map_3684_, lean_object* v_f_3685_, lean_object* v_init_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(v_map_3684_, v_f_3685_, v_init_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object* v_00_u03c3_3693_, lean_object* v_00_u03c3_3694_, lean_object* v_00_u03b2_3695_, lean_object* v_map_3696_, lean_object* v_f_3697_, lean_object* v_init_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_){
_start:
{
lean_object* v___x_3704_; 
v___x_3704_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3697_, v_map_3696_, v_init_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_);
return v___x_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object* v_00_u03c3_3705_, lean_object* v_00_u03c3_3706_, lean_object* v_00_u03b2_3707_, lean_object* v_map_3708_, lean_object* v_f_3709_, lean_object* v_init_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
lean_object* v_res_3716_; 
v_res_3716_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(v_00_u03c3_3705_, v_00_u03c3_3706_, v_00_u03b2_3707_, v_map_3708_, v_f_3709_, v_init_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object* v_00_u03c3_3717_, lean_object* v_00_u03c3_3718_, lean_object* v_00_u03b1_3719_, lean_object* v_00_u03b2_3720_, lean_object* v_f_3721_, lean_object* v_x_3722_, lean_object* v_x_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
lean_object* v___x_3729_; 
v___x_3729_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3721_, v_x_3722_, v_x_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03c3_3730_, lean_object* v_00_u03c3_3731_, lean_object* v_00_u03b1_3732_, lean_object* v_00_u03b2_3733_, lean_object* v_f_3734_, lean_object* v_x_3735_, lean_object* v_x_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(v_00_u03c3_3730_, v_00_u03c3_3731_, v_00_u03b1_3732_, v_00_u03b2_3733_, v_f_3734_, v_x_3735_, v_x_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_3743_, lean_object* v_00_u03b2_3744_, lean_object* v_00_u03c3_3745_, lean_object* v_00_u03c3_3746_, lean_object* v_f_3747_, lean_object* v_as_3748_, size_t v_i_3749_, size_t v_stop_3750_, lean_object* v_b_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_){
_start:
{
lean_object* v___x_3757_; 
v___x_3757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3747_, v_as_3748_, v_i_3749_, v_stop_3750_, v_b_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_3758_, lean_object* v_00_u03b2_3759_, lean_object* v_00_u03c3_3760_, lean_object* v_00_u03c3_3761_, lean_object* v_f_3762_, lean_object* v_as_3763_, lean_object* v_i_3764_, lean_object* v_stop_3765_, lean_object* v_b_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
size_t v_i_boxed_3772_; size_t v_stop_boxed_3773_; lean_object* v_res_3774_; 
v_i_boxed_3772_ = lean_unbox_usize(v_i_3764_);
lean_dec(v_i_3764_);
v_stop_boxed_3773_ = lean_unbox_usize(v_stop_3765_);
lean_dec(v_stop_3765_);
v_res_3774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_3758_, v_00_u03b2_3759_, v_00_u03c3_3760_, v_00_u03c3_3761_, v_f_3762_, v_as_3763_, v_i_boxed_3772_, v_stop_boxed_3773_, v_b_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_);
lean_dec(v___y_3770_);
lean_dec_ref(v___y_3769_);
lean_dec(v___y_3768_);
lean_dec_ref(v___y_3767_);
lean_dec_ref(v_as_3763_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object* v_00_u03c3_3775_, lean_object* v_00_u03c3_3776_, lean_object* v_00_u03b1_3777_, lean_object* v_00_u03b2_3778_, lean_object* v_f_3779_, lean_object* v_keys_3780_, lean_object* v_vals_3781_, lean_object* v_heq_3782_, lean_object* v_i_3783_, lean_object* v_acc_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
lean_object* v___x_3790_; 
v___x_3790_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3779_, v_keys_3780_, v_vals_3781_, v_i_3783_, v_acc_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
return v___x_3790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03c3_3791_, lean_object* v_00_u03c3_3792_, lean_object* v_00_u03b1_3793_, lean_object* v_00_u03b2_3794_, lean_object* v_f_3795_, lean_object* v_keys_3796_, lean_object* v_vals_3797_, lean_object* v_heq_3798_, lean_object* v_i_3799_, lean_object* v_acc_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(v_00_u03c3_3791_, v_00_u03c3_3792_, v_00_u03b1_3793_, v_00_u03b2_3794_, v_f_3795_, v_keys_3796_, v_vals_3797_, v_heq_3798_, v_i_3799_, v_acc_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec_ref(v_vals_3797_);
lean_dec_ref(v_keys_3796_);
return v_res_3806_;
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
