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
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_Parser_ParserExtension_instInhabitedState_default;
extern lean_object* l_Lean_Parser_parserExtension;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_param___override, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0;
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
static const lean_array_object l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_value;
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
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Available tags: "};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1;
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
v___x_21_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_43_; lean_object* v_env_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v_scopes_47_; lean_object* v___x_48_; lean_object* v_opts_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_43_ = lean_st_ref_get(v___y_41_);
v_env_44_ = lean_ctor_get(v___x_43_, 0);
lean_inc_ref(v_env_44_);
lean_dec(v___x_43_);
v___x_45_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_46_ = lean_st_ref_get(v___y_41_);
v_scopes_47_ = lean_ctor_get(v___x_46_, 2);
lean_inc(v_scopes_47_);
lean_dec(v___x_46_);
v___x_48_ = l_List_head_x21___redArg(v___x_45_, v_scopes_47_);
lean_dec(v_scopes_47_);
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
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v_scopes_117_; lean_object* v___x_118_; lean_object* v_opts_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_115_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_116_ = lean_st_ref_get(v___y_113_);
v_scopes_117_ = lean_ctor_get(v___x_116_, 2);
lean_inc(v_scopes_117_);
lean_dec(v___x_116_);
v___x_118_ = l_List_head_x21___redArg(v___x_115_, v_scopes_117_);
lean_dec(v_scopes_117_);
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
lean_object* v_a_152_; lean_object* v_macroStack_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v_a_156_; lean_object* v___x_157_; lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_166_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_a_152_);
lean_dec_ref_known(v___x_151_, 1);
v_macroStack_153_ = lean_ctor_get(v___y_148_, 4);
v___x_154_ = l_Lean_Elab_getBetterRef(v_a_152_, v_macroStack_153_);
lean_dec(v_a_152_);
v___x_155_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msg_147_, v___y_149_);
v_a_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_a_156_);
lean_dec_ref(v___x_155_);
lean_inc(v_macroStack_153_);
v___x_157_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(v_a_156_, v_macroStack_153_, v___y_149_);
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
lean_ctor_set(v___x_162_, 0, v___x_154_);
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
lean_dec(v_kind_486_);
lean_dec_ref_known(v___x_484_, 3);
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
lean_object* v___x_554_; lean_object* v_toEnvExtension_555_; lean_object* v_asyncMode_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_554_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_555_ = lean_ctor_get(v___x_554_, 0);
v_asyncMode_556_ = lean_ctor_get(v_toEnvExtension_555_, 2);
v___x_557_ = lean_box(0);
v___x_558_ = l_Lean_TSyntax_getId(v___y_535_);
lean_dec(v___y_535_);
v___x_559_ = l_Lean_TSyntax_getString(v___y_533_);
lean_dec(v___y_533_);
v___x_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set(v___x_560_, 1, v_a_536_);
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_558_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = lean_box(0);
v___x_563_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_554_, v_env_538_, v___x_561_, v_asyncMode_556_, v___x_562_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_563_);
v___x_565_ = v___x_552_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_563_);
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
v___x_565_ = v_reuseFailAlloc_568_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_st_ref_put(v___y_534_, v___x_565_);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_557_);
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
size_t v_x_3827__boxed_1057_; uint8_t v_res_1058_; lean_object* v_r_1059_; 
v_x_3827__boxed_1057_ = lean_unbox_usize(v_x_1055_);
lean_dec(v_x_1055_);
v_res_1058_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1054_, v_x_3827__boxed_1057_, v_x_1056_);
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
uint8_t v___x_3883__boxed_1089_; lean_object* v_res_1090_; 
v___x_3883__boxed_1089_ = lean_unbox(v___x_1086_);
v_res_1090_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(v_tactics_1084_, v_a_1085_, v___x_3883__boxed_1089_, v_x_1087_, v_____s_1088_);
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
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0);
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(lean_object* v_tactics_1196_, lean_object* v_a_1197_, uint8_t v___x_1198_, lean_object* v_as_x27_1199_, lean_object* v_b_1200_){
_start:
{
if (lean_obj_tag(v_as_x27_1199_) == 0)
{
lean_dec(v_a_1197_);
lean_dec_ref(v_tactics_1196_);
return v_b_1200_;
}
else
{
lean_object* v_head_1201_; lean_object* v_fst_1202_; lean_object* v_info_1203_; lean_object* v_tail_1204_; lean_object* v_collectKinds_1205_; lean_object* v___x_1206_; lean_object* v___f_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v_head_1201_ = lean_ctor_get(v_as_x27_1199_, 0);
v_fst_1202_ = lean_ctor_get(v_head_1201_, 0);
v_info_1203_ = lean_ctor_get(v_fst_1202_, 0);
v_tail_1204_ = lean_ctor_get(v_as_x27_1199_, 1);
v_collectKinds_1205_ = lean_ctor_get(v_info_1203_, 1);
v___x_1206_ = lean_box(v___x_1198_);
lean_inc(v_a_1197_);
lean_inc_ref(v_tactics_1196_);
v___f_1207_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1207_, 0, v_tactics_1196_);
lean_closure_set(v___f_1207_, 1, v_a_1197_);
lean_closure_set(v___f_1207_, 2, v___x_1206_);
v___x_1208_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0);
lean_inc_ref(v_collectKinds_1205_);
v___x_1209_ = lean_apply_1(v_collectKinds_1205_, v___x_1208_);
v___x_1210_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v___x_1209_, v_b_1200_, v___f_1207_);
lean_dec_ref(v___x_1209_);
v_as_x27_1199_ = v_tail_1204_;
v_b_1200_ = v___x_1210_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(lean_object* v_tactics_1212_, lean_object* v_a_1213_, lean_object* v___x_1214_, lean_object* v_as_x27_1215_, lean_object* v_b_1216_){
_start:
{
uint8_t v___x_4042__boxed_1217_; lean_object* v_res_1218_; 
v___x_4042__boxed_1217_ = lean_unbox(v___x_1214_);
v_res_1218_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1212_, v_a_1213_, v___x_4042__boxed_1217_, v_as_x27_1215_, v_b_1216_);
lean_dec(v_as_x27_1215_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(lean_object* v_tactics_1222_, lean_object* v_init_1223_, lean_object* v_x_1224_){
_start:
{
if (lean_obj_tag(v_x_1224_) == 0)
{
lean_object* v_k_1225_; lean_object* v_v_1226_; lean_object* v_l_1227_; lean_object* v_r_1228_; lean_object* v___x_1229_; lean_object* v_a_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v_k_1225_ = lean_ctor_get(v_x_1224_, 1);
lean_inc(v_k_1225_);
v_v_1226_ = lean_ctor_get(v_x_1224_, 2);
lean_inc(v_v_1226_);
v_l_1227_ = lean_ctor_get(v_x_1224_, 3);
lean_inc(v_l_1227_);
v_r_1228_ = lean_ctor_get(v_x_1224_, 4);
lean_inc(v_r_1228_);
lean_dec_ref_known(v_x_1224_, 5);
lean_inc_ref(v_tactics_1222_);
v___x_1229_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_1222_, v_init_1223_, v_l_1227_);
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1230_);
v___x_1231_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1));
v___x_1232_ = lean_name_eq(v_k_1225_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; 
lean_dec_ref(v___x_1229_);
lean_inc_ref(v_tactics_1222_);
v___x_1233_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1222_, v_k_1225_, v___x_1232_, v_v_1226_, v_a_1230_);
lean_dec(v_v_1226_);
v_init_1223_ = v___x_1233_;
v_x_1224_ = v_r_1228_;
goto _start;
}
else
{
lean_object* v_a_1235_; 
lean_dec(v_a_1230_);
lean_dec(v_v_1226_);
lean_dec(v_k_1225_);
v_a_1235_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1235_);
lean_dec_ref(v___x_1229_);
v_init_1223_ = v_a_1235_;
v_x_1224_ = v_r_1228_;
goto _start;
}
}
else
{
lean_object* v___x_1237_; 
lean_dec_ref(v_tactics_1222_);
v___x_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1237_, 0, v_init_1223_);
return v___x_1237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(lean_object* v_tactics_1238_, lean_object* v_table_1239_, lean_object* v_firsts_1240_){
_start:
{
lean_object* v___x_1241_; lean_object* v_a_1242_; 
v___x_1241_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_1238_, v_firsts_1240_, v_table_1239_);
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref(v___x_1241_);
return v_a_1242_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_object* v_00_u03b2_1243_, lean_object* v_x_1244_, lean_object* v_x_1245_){
_start:
{
uint8_t v___x_1246_; 
v___x_1246_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_1244_, v_x_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(lean_object* v_00_u03b2_1247_, lean_object* v_x_1248_, lean_object* v_x_1249_){
_start:
{
uint8_t v_res_1250_; lean_object* v_r_1251_; 
v_res_1250_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(v_00_u03b2_1247_, v_x_1248_, v_x_1249_);
lean_dec(v_x_1249_);
lean_dec_ref(v_x_1248_);
v_r_1251_ = lean_box(v_res_1250_);
return v_r_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(lean_object* v___x_1252_, lean_object* v_k_1253_, lean_object* v_t_1254_, lean_object* v_hl_1255_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1252_, v_k_1253_, v_t_1254_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(lean_object* v_00_u03c3_1257_, lean_object* v_00_u03b2_1258_, lean_object* v_map_1259_, lean_object* v_init_1260_, lean_object* v_f_1261_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_1259_, v_init_1260_, v_f_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___boxed(lean_object* v_00_u03c3_1263_, lean_object* v_00_u03b2_1264_, lean_object* v_map_1265_, lean_object* v_init_1266_, lean_object* v_f_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(v_00_u03c3_1263_, v_00_u03b2_1264_, v_map_1265_, v_init_1266_, v_f_1267_);
lean_dec_ref(v_map_1265_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(lean_object* v_tactics_1269_, lean_object* v_a_1270_, uint8_t v___x_1271_, lean_object* v_as_1272_, lean_object* v_as_x27_1273_, lean_object* v_b_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1269_, v_a_1270_, v___x_1271_, v_as_x27_1273_, v_b_1274_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(lean_object* v_tactics_1277_, lean_object* v_a_1278_, lean_object* v___x_1279_, lean_object* v_as_1280_, lean_object* v_as_x27_1281_, lean_object* v_b_1282_, lean_object* v_a_1283_){
_start:
{
uint8_t v___x_4124__boxed_1284_; lean_object* v_res_1285_; 
v___x_4124__boxed_1284_ = lean_unbox(v___x_1279_);
v_res_1285_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(v_tactics_1277_, v_a_1278_, v___x_4124__boxed_1284_, v_as_1280_, v_as_x27_1281_, v_b_1282_, v_a_1283_);
lean_dec(v_as_x27_1281_);
lean_dec(v_as_1280_);
return v_res_1285_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_object* v_00_u03b2_1286_, lean_object* v_x_1287_, size_t v_x_1288_, lean_object* v_x_1289_){
_start:
{
uint8_t v___x_1290_; 
v___x_1290_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1287_, v_x_1288_, v_x_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1291_, lean_object* v_x_1292_, lean_object* v_x_1293_, lean_object* v_x_1294_){
_start:
{
size_t v_x_4133__boxed_1295_; uint8_t v_res_1296_; lean_object* v_r_1297_; 
v_x_4133__boxed_1295_ = lean_unbox_usize(v_x_1293_);
lean_dec(v_x_1293_);
v_res_1296_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(v_00_u03b2_1291_, v_x_1292_, v_x_4133__boxed_1295_, v_x_1294_);
lean_dec(v_x_1294_);
lean_dec_ref(v_x_1292_);
v_r_1297_ = lean_box(v_res_1296_);
return v_r_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(lean_object* v_map_1298_, lean_object* v_f_1299_, lean_object* v_init_1300_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1299_, v_map_1298_, v_init_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(lean_object* v_00_u03c3_1302_, lean_object* v_00_u03c3_1303_, lean_object* v_00_u03b2_1304_, lean_object* v_map_1305_, lean_object* v_f_1306_, lean_object* v_init_1307_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1306_, v_map_1305_, v_init_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1309_, lean_object* v_keys_1310_, lean_object* v_vals_1311_, lean_object* v_heq_1312_, lean_object* v_i_1313_, lean_object* v_k_1314_){
_start:
{
uint8_t v___x_1315_; 
v___x_1315_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_1310_, v_i_1313_, v_k_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1316_, lean_object* v_keys_1317_, lean_object* v_vals_1318_, lean_object* v_heq_1319_, lean_object* v_i_1320_, lean_object* v_k_1321_){
_start:
{
uint8_t v_res_1322_; lean_object* v_r_1323_; 
v_res_1322_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(v_00_u03b2_1316_, v_keys_1317_, v_vals_1318_, v_heq_1319_, v_i_1320_, v_k_1321_);
lean_dec(v_k_1321_);
lean_dec_ref(v_vals_1318_);
lean_dec_ref(v_keys_1317_);
v_r_1323_ = lean_box(v_res_1322_);
return v_r_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(lean_object* v_00_u03c3_1324_, lean_object* v_00_u03c3_1325_, lean_object* v_00_u03b1_1326_, lean_object* v_00_u03b2_1327_, lean_object* v_f_1328_, lean_object* v_x_1329_, lean_object* v_x_1330_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1328_, v_x_1329_, v_x_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b1_1332_, lean_object* v_00_u03b2_1333_, lean_object* v_00_u03c3_1334_, lean_object* v_00_u03c3_1335_, lean_object* v_f_1336_, lean_object* v_as_1337_, size_t v_i_1338_, size_t v_stop_1339_, lean_object* v_b_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1336_, v_as_1337_, v_i_1338_, v_stop_1339_, v_b_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1342_, lean_object* v_00_u03b2_1343_, lean_object* v_00_u03c3_1344_, lean_object* v_00_u03c3_1345_, lean_object* v_f_1346_, lean_object* v_as_1347_, lean_object* v_i_1348_, lean_object* v_stop_1349_, lean_object* v_b_1350_){
_start:
{
size_t v_i_boxed_1351_; size_t v_stop_boxed_1352_; lean_object* v_res_1353_; 
v_i_boxed_1351_ = lean_unbox_usize(v_i_1348_);
lean_dec(v_i_1348_);
v_stop_boxed_1352_ = lean_unbox_usize(v_stop_1349_);
lean_dec(v_stop_1349_);
v_res_1353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(v_00_u03b1_1342_, v_00_u03b2_1343_, v_00_u03c3_1344_, v_00_u03c3_1345_, v_f_1346_, v_as_1347_, v_i_boxed_1351_, v_stop_boxed_1352_, v_b_1350_);
lean_dec_ref(v_as_1347_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03c3_1354_, lean_object* v_00_u03c3_1355_, lean_object* v_00_u03b1_1356_, lean_object* v_00_u03b2_1357_, lean_object* v_f_1358_, lean_object* v_keys_1359_, lean_object* v_vals_1360_, lean_object* v_heq_1361_, lean_object* v_i_1362_, lean_object* v_acc_1363_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1358_, v_keys_1359_, v_vals_1360_, v_i_1362_, v_acc_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03c3_1365_, lean_object* v_00_u03c3_1366_, lean_object* v_00_u03b1_1367_, lean_object* v_00_u03b2_1368_, lean_object* v_f_1369_, lean_object* v_keys_1370_, lean_object* v_vals_1371_, lean_object* v_heq_1372_, lean_object* v_i_1373_, lean_object* v_acc_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(v_00_u03c3_1365_, v_00_u03c3_1366_, v_00_u03b1_1367_, v_00_u03b2_1368_, v_f_1369_, v_keys_1370_, v_vals_1371_, v_heq_1372_, v_i_1373_, v_acc_1374_);
lean_dec_ref(v_vals_1371_);
lean_dec_ref(v_keys_1370_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(lean_object* v_x1_1376_, lean_object* v_x2_1377_){
_start:
{
lean_object* v_fst_1378_; lean_object* v_snd_1379_; lean_object* v___x_1380_; 
v_fst_1378_ = lean_ctor_get(v_x2_1377_, 0);
lean_inc(v_fst_1378_);
v_snd_1379_ = lean_ctor_get(v_x2_1377_, 1);
lean_inc(v_snd_1379_);
lean_dec_ref(v_x2_1377_);
v___x_1380_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1378_, v_snd_1379_, v_x1_1376_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(lean_object* v___f_1400_, lean_object* v_x1_1401_, lean_object* v_x2_1402_){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v___x_1403_ = lean_unsigned_to_nat(0u);
v___x_1404_ = lean_array_get_size(v_x2_1402_);
v___x_1405_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_1406_ = lean_nat_dec_lt(v___x_1403_, v___x_1404_);
if (v___x_1406_ == 0)
{
lean_dec_ref(v_x2_1402_);
lean_dec_ref(v___f_1400_);
return v_x1_1401_;
}
else
{
uint8_t v___x_1407_; 
v___x_1407_ = lean_nat_dec_le(v___x_1404_, v___x_1404_);
if (v___x_1407_ == 0)
{
if (v___x_1406_ == 0)
{
lean_dec_ref(v_x2_1402_);
lean_dec_ref(v___f_1400_);
return v_x1_1401_;
}
else
{
size_t v___x_1408_; size_t v___x_1409_; lean_object* v___x_1410_; 
v___x_1408_ = ((size_t)0ULL);
v___x_1409_ = lean_usize_of_nat(v___x_1404_);
v___x_1410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1405_, v___f_1400_, v_x2_1402_, v___x_1408_, v___x_1409_, v_x1_1401_);
return v___x_1410_;
}
}
else
{
size_t v___x_1411_; size_t v___x_1412_; lean_object* v___x_1413_; 
v___x_1411_ = ((size_t)0ULL);
v___x_1412_ = lean_usize_of_nat(v___x_1404_);
v___x_1413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1405_, v___f_1400_, v_x2_1402_, v___x_1411_, v___x_1412_, v_x1_1401_);
return v___x_1413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object* v___x_1417_, lean_object* v___x_1418_, lean_object* v___x_1419_, lean_object* v___x_1420_, lean_object* v___x_1421_, lean_object* v_toPure_1422_, lean_object* v___f_1423_, lean_object* v_env_1424_){
_start:
{
lean_object* v___x_1425_; lean_object* v_ext_1426_; lean_object* v_toEnvExtension_1427_; lean_object* v_asyncMode_1428_; lean_object* v___x_1429_; lean_object* v_categories_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1425_ = l_Lean_Parser_parserExtension;
v_ext_1426_ = lean_ctor_get(v___x_1425_, 1);
v_toEnvExtension_1427_ = lean_ctor_get(v_ext_1426_, 0);
v_asyncMode_1428_ = lean_ctor_get(v_toEnvExtension_1427_, 2);
lean_inc_ref(v_env_1424_);
v___x_1429_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1417_, v___x_1425_, v_env_1424_, v_asyncMode_1428_);
v_categories_1430_ = lean_ctor_get(v___x_1429_, 2);
lean_inc_ref(v_categories_1430_);
lean_dec(v___x_1429_);
v___x_1431_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_1432_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_1418_, v___x_1419_, v_categories_1430_, v___x_1431_);
lean_dec_ref(v_categories_1430_);
if (lean_obj_tag(v___x_1432_) == 1)
{
lean_object* v_val_1433_; lean_object* v___y_1435_; lean_object* v___x_1442_; lean_object* v_toEnvExtension_1443_; lean_object* v_exportEntriesFn_1444_; lean_object* v_asyncMode_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v_importedEntries_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v_exported_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
v_val_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_val_1433_);
lean_dec_ref_known(v___x_1432_, 1);
v___x_1442_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1443_ = lean_ctor_get(v___x_1442_, 0);
v_exportEntriesFn_1444_ = lean_ctor_get(v___x_1442_, 4);
v_asyncMode_1445_ = lean_ctor_get(v_toEnvExtension_1443_, 2);
v___x_1446_ = lean_box(0);
lean_inc_ref_n(v_env_1424_, 2);
v___x_1447_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1420_, v_toEnvExtension_1443_, v_env_1424_, v_asyncMode_1445_, v___x_1446_);
v_importedEntries_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc_ref(v_importedEntries_1448_);
lean_dec(v___x_1447_);
v___x_1449_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1421_, v___x_1442_, v_env_1424_, v_asyncMode_1445_, v___x_1446_);
lean_inc_ref(v_exportEntriesFn_1444_);
v___x_1450_ = lean_apply_2(v_exportEntriesFn_1444_, v_env_1424_, v___x_1449_);
v_exported_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_exported_1451_);
lean_dec_ref(v___x_1450_);
v___x_1452_ = lean_box(1);
v___x_1453_ = lean_array_push(v_importedEntries_1448_, v_exported_1451_);
v___x_1454_ = lean_unsigned_to_nat(0u);
v___x_1455_ = lean_array_get_size(v___x_1453_);
v___x_1456_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_1457_ = lean_nat_dec_lt(v___x_1454_, v___x_1455_);
if (v___x_1457_ == 0)
{
lean_dec_ref(v___x_1453_);
lean_dec_ref(v___f_1423_);
v___y_1435_ = v___x_1452_;
goto v___jp_1434_;
}
else
{
uint8_t v___x_1458_; 
v___x_1458_ = lean_nat_dec_le(v___x_1455_, v___x_1455_);
if (v___x_1458_ == 0)
{
if (v___x_1457_ == 0)
{
lean_dec_ref(v___x_1453_);
lean_dec_ref(v___f_1423_);
v___y_1435_ = v___x_1452_;
goto v___jp_1434_;
}
else
{
size_t v___x_1459_; size_t v___x_1460_; lean_object* v___x_1461_; 
v___x_1459_ = ((size_t)0ULL);
v___x_1460_ = lean_usize_of_nat(v___x_1455_);
v___x_1461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1456_, v___f_1423_, v___x_1453_, v___x_1459_, v___x_1460_, v___x_1452_);
v___y_1435_ = v___x_1461_;
goto v___jp_1434_;
}
}
else
{
size_t v___x_1462_; size_t v___x_1463_; lean_object* v___x_1464_; 
v___x_1462_ = ((size_t)0ULL);
v___x_1463_ = lean_usize_of_nat(v___x_1455_);
v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1456_, v___f_1423_, v___x_1453_, v___x_1462_, v___x_1463_, v___x_1452_);
v___y_1435_ = v___x_1464_;
goto v___jp_1434_;
}
}
v___jp_1434_:
{
lean_object* v_tables_1436_; lean_object* v_leadingTable_1437_; lean_object* v_trailingTable_1438_; lean_object* v_firstTokens_1439_; lean_object* v_firstTokens_1440_; lean_object* v___x_1441_; 
v_tables_1436_ = lean_ctor_get(v_val_1433_, 2);
v_leadingTable_1437_ = lean_ctor_get(v_tables_1436_, 0);
v_trailingTable_1438_ = lean_ctor_get(v_tables_1436_, 2);
lean_inc(v_trailingTable_1438_);
lean_inc(v_leadingTable_1437_);
lean_inc(v_val_1433_);
v_firstTokens_1439_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_1433_, v_leadingTable_1437_, v___y_1435_);
v_firstTokens_1440_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_1433_, v_trailingTable_1438_, v_firstTokens_1439_);
v___x_1441_ = lean_apply_2(v_toPure_1422_, lean_box(0), v_firstTokens_1440_);
return v___x_1441_;
}
}
else
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
lean_dec(v___x_1432_);
lean_dec_ref(v_env_1424_);
lean_dec_ref(v___f_1423_);
lean_dec(v___x_1421_);
v___x_1465_ = lean_box(1);
v___x_1466_ = lean_apply_2(v_toPure_1422_, lean_box(0), v___x_1465_);
return v___x_1466_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed(lean_object* v___x_1467_, lean_object* v___x_1468_, lean_object* v___x_1469_, lean_object* v___x_1470_, lean_object* v___x_1471_, lean_object* v_toPure_1472_, lean_object* v___f_1473_, lean_object* v_env_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(v___x_1467_, v___x_1468_, v___x_1469_, v___x_1470_, v___x_1471_, v_toPure_1472_, v___f_1473_, v_env_1474_);
lean_dec_ref(v___x_1470_);
lean_dec_ref(v___x_1467_);
return v_res_1475_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = lean_box(1);
v___x_1480_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object* v_inst_1483_, lean_object* v_inst_1484_){
_start:
{
lean_object* v_toApplicative_1485_; lean_object* v_toBind_1486_; lean_object* v_getEnv_1487_; lean_object* v_toPure_1488_; lean_object* v___f_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___f_1495_; lean_object* v___x_1496_; 
v_toApplicative_1485_ = lean_ctor_get(v_inst_1483_, 0);
lean_inc_ref(v_toApplicative_1485_);
v_toBind_1486_ = lean_ctor_get(v_inst_1483_, 1);
lean_inc(v_toBind_1486_);
lean_dec_ref(v_inst_1483_);
v_getEnv_1487_ = lean_ctor_get(v_inst_1484_, 0);
lean_inc(v_getEnv_1487_);
lean_dec_ref(v_inst_1484_);
v_toPure_1488_ = lean_ctor_get(v_toApplicative_1485_, 1);
lean_inc(v_toPure_1488_);
lean_dec_ref(v_toApplicative_1485_);
v___f_1489_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1));
v___x_1490_ = lean_box(1);
v___x_1491_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_1492_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_1493_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___x_1494_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___f_1495_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1495_, 0, v___x_1494_);
lean_closure_set(v___f_1495_, 1, v___x_1492_);
lean_closure_set(v___f_1495_, 2, v___x_1493_);
lean_closure_set(v___f_1495_, 3, v___x_1491_);
lean_closure_set(v___f_1495_, 4, v___x_1490_);
lean_closure_set(v___f_1495_, 5, v_toPure_1488_);
lean_closure_set(v___f_1495_, 6, v___f_1489_);
v___x_1496_ = lean_apply_4(v_toBind_1486_, lean_box(0), lean_box(0), v_getEnv_1487_, v___f_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object* v_m_1497_, lean_object* v_inst_1498_, lean_object* v_inst_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(v_inst_1498_, v_inst_1499_);
return v___x_1500_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0);
v___x_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1501_);
return v___x_1502_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1503_ = lean_box(1);
v___x_1504_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4);
v___x_1505_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0);
v___x_1506_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
lean_ctor_set(v___x_1506_, 1, v___x_1504_);
lean_ctor_set(v___x_1506_, 2, v___x_1503_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object* v_n_1508_, lean_object* v___y_1509_, lean_object* v_toPure_1510_, lean_object* v_firsts_1511_, lean_object* v_____do__lift_1512_){
_start:
{
lean_object* v___y_1514_; lean_object* v_val_1525_; 
if (lean_obj_tag(v_____do__lift_1512_) == 0)
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2));
lean_inc(v_n_1508_);
v___x_1528_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_1527_, v_firsts_1511_, v_n_1508_);
if (lean_obj_tag(v___x_1528_) == 0)
{
uint8_t v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1529_ = 1;
lean_inc(v_n_1508_);
v___x_1530_ = l_Lean_Name_toString(v_n_1508_, v___x_1529_);
v___x_1531_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
v___y_1514_ = v___x_1531_;
goto v___jp_1513_;
}
else
{
lean_object* v_val_1532_; 
v_val_1532_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_val_1532_);
lean_dec_ref_known(v___x_1528_, 1);
v_val_1525_ = v_val_1532_;
goto v___jp_1524_;
}
}
else
{
lean_object* v_val_1533_; 
lean_dec(v_firsts_1511_);
v_val_1533_ = lean_ctor_get(v_____do__lift_1512_, 0);
lean_inc(v_val_1533_);
lean_dec_ref_known(v_____do__lift_1512_, 1);
v_val_1525_ = v_val_1533_;
goto v___jp_1524_;
}
v___jp_1513_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1515_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8);
v___x_1516_ = l_Lean_Expr_const___override(v_n_1508_, v___y_1509_);
v___x_1517_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1);
v___x_1518_ = lean_box(0);
v___x_1519_ = 0;
v___x_1520_ = l_Lean_MessageData_withExprHover(v___y_1514_, v___x_1516_, v___x_1517_, v___x_1518_, v___x_1518_, v___x_1518_, v___x_1519_);
v___x_1521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1515_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
v___x_1522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
lean_ctor_set(v___x_1522_, 1, v___x_1515_);
v___x_1523_ = lean_apply_2(v_toPure_1510_, lean_box(0), v___x_1522_);
return v___x_1523_;
}
v___jp_1524_:
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1526_, 0, v_val_1525_);
v___y_1514_ = v___x_1526_;
goto v___jp_1513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object* v_n_1534_, lean_object* v_toPure_1535_, lean_object* v_firsts_1536_, lean_object* v_inst_1537_, lean_object* v_inst_1538_, lean_object* v_toBind_1539_, lean_object* v___x_1540_, lean_object* v___x_1541_, lean_object* v___f_1542_, lean_object* v_env_1543_){
_start:
{
lean_object* v___y_1545_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = l_Lean_Environment_constants(v_env_1543_);
lean_inc(v_n_1534_);
v___x_1550_ = l_Lean_SMap_find_x3f_x27___redArg(v___x_1540_, v___x_1541_, v___x_1549_, v_n_1534_);
lean_dec_ref(v___x_1549_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v___x_1551_; 
lean_dec_ref(v___f_1542_);
v___x_1551_ = lean_box(0);
v___y_1545_ = v___x_1551_;
goto v___jp_1544_;
}
else
{
lean_object* v_val_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v_val_1552_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_val_1552_);
lean_dec_ref_known(v___x_1550_, 1);
v___x_1553_ = l_Lean_ConstantInfo_levelParams(v_val_1552_);
lean_dec(v_val_1552_);
v___x_1554_ = lean_box(0);
v___x_1555_ = l_List_mapTR_loop___redArg(v___f_1542_, v___x_1553_, v___x_1554_);
v___y_1545_ = v___x_1555_;
goto v___jp_1544_;
}
v___jp_1544_:
{
lean_object* v___f_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
lean_inc(v_n_1534_);
v___f_1546_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1546_, 0, v_n_1534_);
lean_closure_set(v___f_1546_, 1, v___y_1545_);
lean_closure_set(v___f_1546_, 2, v_toPure_1535_);
lean_closure_set(v___f_1546_, 3, v_firsts_1536_);
v___x_1547_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(v_inst_1537_, v_inst_1538_, v_n_1534_);
v___x_1548_ = lean_apply_4(v_toBind_1539_, lean_box(0), lean_box(0), v___x_1547_, v___f_1546_);
return v___x_1548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object* v_inst_1557_, lean_object* v_inst_1558_, lean_object* v_firsts_1559_, lean_object* v_n_1560_){
_start:
{
lean_object* v_toApplicative_1561_; lean_object* v_toBind_1562_; lean_object* v_getEnv_1563_; lean_object* v_toPure_1564_; lean_object* v___f_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___f_1568_; lean_object* v___x_1569_; 
v_toApplicative_1561_ = lean_ctor_get(v_inst_1557_, 0);
v_toBind_1562_ = lean_ctor_get(v_inst_1557_, 1);
lean_inc_n(v_toBind_1562_, 2);
v_getEnv_1563_ = lean_ctor_get(v_inst_1558_, 0);
lean_inc(v_getEnv_1563_);
v_toPure_1564_ = lean_ctor_get(v_toApplicative_1561_, 1);
lean_inc(v_toPure_1564_);
v___f_1565_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0));
v___x_1566_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_1567_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___f_1568_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1568_, 0, v_n_1560_);
lean_closure_set(v___f_1568_, 1, v_toPure_1564_);
lean_closure_set(v___f_1568_, 2, v_firsts_1559_);
lean_closure_set(v___f_1568_, 3, v_inst_1557_);
lean_closure_set(v___f_1568_, 4, v_inst_1558_);
lean_closure_set(v___f_1568_, 5, v_toBind_1562_);
lean_closure_set(v___f_1568_, 6, v___x_1566_);
lean_closure_set(v___f_1568_, 7, v___x_1567_);
lean_closure_set(v___f_1568_, 8, v___f_1565_);
v___x_1569_ = lean_apply_4(v_toBind_1562_, lean_box(0), lean_box(0), v_getEnv_1563_, v___f_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object* v_m_1570_, lean_object* v_inst_1571_, lean_object* v_inst_1572_, lean_object* v_firsts_1573_, lean_object* v_n_1574_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(v_inst_1571_, v_inst_1572_, v_firsts_1573_, v_n_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg(){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___closed__0));
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___boxed(lean_object* v___dummy_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg();
return v_res_1581_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg();
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object* v_s_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object* v_s_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v_s_1585_);
lean_dec_ref(v_s_1585_);
return v_res_1586_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t v___x_1587_, lean_object* v_x1_1588_, lean_object* v_x2_1589_){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1590_ = l_Lean_Name_toString(v_x1_1588_, v___x_1587_);
v___x_1591_ = l_Lean_Name_toString(v_x2_1589_, v___x_1587_);
v___x_1592_ = lean_string_dec_lt(v___x_1590_, v___x_1591_);
lean_dec_ref(v___x_1591_);
lean_dec_ref(v___x_1590_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object* v___x_1593_, lean_object* v_x1_1594_, lean_object* v_x2_1595_){
_start:
{
uint8_t v___x_16934__boxed_1596_; uint8_t v_res_1597_; lean_object* v_r_1598_; 
v___x_16934__boxed_1596_ = lean_unbox(v___x_1593_);
v_res_1597_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_16934__boxed_1596_, v_x1_1594_, v_x2_1595_);
v_r_1598_ = lean_box(v_res_1597_);
return v_r_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(lean_object* v_hi_1599_, lean_object* v_pivot_1600_, lean_object* v_as_1601_, lean_object* v_i_1602_, lean_object* v_k_1603_){
_start:
{
uint8_t v___x_1604_; 
v___x_1604_ = lean_nat_dec_lt(v_k_1603_, v_hi_1599_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
lean_dec(v_k_1603_);
lean_dec(v_pivot_1600_);
v___x_1605_ = lean_array_fswap(v_as_1601_, v_i_1602_, v_hi_1599_);
v___x_1606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1606_, 0, v_i_1602_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
return v___x_1606_;
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1607_ = lean_array_fget_borrowed(v_as_1601_, v_k_1603_);
lean_inc(v___x_1607_);
v___x_1608_ = l_Lean_Name_toString(v___x_1607_, v___x_1604_);
lean_inc(v_pivot_1600_);
v___x_1609_ = l_Lean_Name_toString(v_pivot_1600_, v___x_1604_);
v___x_1610_ = lean_string_dec_lt(v___x_1608_, v___x_1609_);
lean_dec_ref(v___x_1609_);
lean_dec_ref(v___x_1608_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_unsigned_to_nat(1u);
v___x_1612_ = lean_nat_add(v_k_1603_, v___x_1611_);
lean_dec(v_k_1603_);
v_k_1603_ = v___x_1612_;
goto _start;
}
else
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1614_ = lean_array_fswap(v_as_1601_, v_i_1602_, v_k_1603_);
v___x_1615_ = lean_unsigned_to_nat(1u);
v___x_1616_ = lean_nat_add(v_i_1602_, v___x_1615_);
lean_dec(v_i_1602_);
v___x_1617_ = lean_nat_add(v_k_1603_, v___x_1615_);
lean_dec(v_k_1603_);
v_as_1601_ = v___x_1614_;
v_i_1602_ = v___x_1616_;
v_k_1603_ = v___x_1617_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg___boxed(lean_object* v_hi_1619_, lean_object* v_pivot_1620_, lean_object* v_as_1621_, lean_object* v_i_1622_, lean_object* v_k_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_1619_, v_pivot_1620_, v_as_1621_, v_i_1622_, v_k_1623_);
lean_dec(v_hi_1619_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object* v_n_1625_, lean_object* v_as_1626_, lean_object* v_lo_1627_, lean_object* v_hi_1628_){
_start:
{
lean_object* v___y_1630_; uint8_t v___x_1640_; 
v___x_1640_ = lean_nat_dec_lt(v_lo_1627_, v_hi_1628_);
if (v___x_1640_ == 0)
{
lean_dec(v_lo_1627_);
return v_as_1626_;
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v_mid_1643_; lean_object* v___y_1645_; lean_object* v___y_1651_; lean_object* v___x_1656_; lean_object* v___x_1657_; uint8_t v___x_1658_; 
v___x_1641_ = lean_nat_add(v_lo_1627_, v_hi_1628_);
v___x_1642_ = lean_unsigned_to_nat(1u);
v_mid_1643_ = lean_nat_shiftr(v___x_1641_, v___x_1642_);
lean_dec(v___x_1641_);
v___x_1656_ = lean_array_fget_borrowed(v_as_1626_, v_mid_1643_);
v___x_1657_ = lean_array_fget_borrowed(v_as_1626_, v_lo_1627_);
lean_inc(v___x_1657_);
lean_inc(v___x_1656_);
v___x_1658_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1640_, v___x_1656_, v___x_1657_);
if (v___x_1658_ == 0)
{
v___y_1651_ = v_as_1626_;
goto v___jp_1650_;
}
else
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_array_fswap(v_as_1626_, v_lo_1627_, v_mid_1643_);
v___y_1651_ = v___x_1659_;
goto v___jp_1650_;
}
v___jp_1644_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; uint8_t v___x_1648_; 
v___x_1646_ = lean_array_fget_borrowed(v___y_1645_, v_mid_1643_);
v___x_1647_ = lean_array_fget_borrowed(v___y_1645_, v_hi_1628_);
lean_inc(v___x_1647_);
lean_inc(v___x_1646_);
v___x_1648_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1640_, v___x_1646_, v___x_1647_);
if (v___x_1648_ == 0)
{
lean_dec(v_mid_1643_);
v___y_1630_ = v___y_1645_;
goto v___jp_1629_;
}
else
{
lean_object* v___x_1649_; 
v___x_1649_ = lean_array_fswap(v___y_1645_, v_mid_1643_, v_hi_1628_);
lean_dec(v_mid_1643_);
v___y_1630_ = v___x_1649_;
goto v___jp_1629_;
}
}
v___jp_1650_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; 
v___x_1652_ = lean_array_fget_borrowed(v___y_1651_, v_hi_1628_);
v___x_1653_ = lean_array_fget_borrowed(v___y_1651_, v_lo_1627_);
lean_inc(v___x_1653_);
lean_inc(v___x_1652_);
v___x_1654_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1640_, v___x_1652_, v___x_1653_);
if (v___x_1654_ == 0)
{
v___y_1645_ = v___y_1651_;
goto v___jp_1644_;
}
else
{
lean_object* v___x_1655_; 
v___x_1655_ = lean_array_fswap(v___y_1651_, v_lo_1627_, v_hi_1628_);
v___y_1645_ = v___x_1655_;
goto v___jp_1644_;
}
}
}
v___jp_1629_:
{
lean_object* v_pivot_1631_; lean_object* v___x_1632_; lean_object* v_fst_1633_; lean_object* v_snd_1634_; uint8_t v___x_1635_; 
v_pivot_1631_ = lean_array_fget(v___y_1630_, v_hi_1628_);
lean_inc_n(v_lo_1627_, 2);
v___x_1632_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_1628_, v_pivot_1631_, v___y_1630_, v_lo_1627_, v_lo_1627_);
v_fst_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_fst_1633_);
v_snd_1634_ = lean_ctor_get(v___x_1632_, 1);
lean_inc(v_snd_1634_);
lean_dec_ref(v___x_1632_);
v___x_1635_ = lean_nat_dec_le(v_hi_1628_, v_fst_1633_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1636_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_1625_, v_snd_1634_, v_lo_1627_, v_fst_1633_);
v___x_1637_ = lean_unsigned_to_nat(1u);
v___x_1638_ = lean_nat_add(v_fst_1633_, v___x_1637_);
lean_dec(v_fst_1633_);
v_as_1626_ = v___x_1636_;
v_lo_1627_ = v___x_1638_;
goto _start;
}
else
{
lean_dec(v_fst_1633_);
lean_dec(v_lo_1627_);
return v_snd_1634_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object* v_n_1660_, lean_object* v_as_1661_, lean_object* v_lo_1662_, lean_object* v_hi_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_1660_, v_as_1661_, v_lo_1662_, v_hi_1663_);
lean_dec(v_hi_1663_);
lean_dec(v_n_1660_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(lean_object* v_init_1665_, lean_object* v_x_1666_){
_start:
{
if (lean_obj_tag(v_x_1666_) == 0)
{
lean_object* v_k_1667_; lean_object* v_l_1668_; lean_object* v_r_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v_k_1667_ = lean_ctor_get(v_x_1666_, 1);
lean_inc(v_k_1667_);
v_l_1668_ = lean_ctor_get(v_x_1666_, 3);
lean_inc(v_l_1668_);
v_r_1669_ = lean_ctor_get(v_x_1666_, 4);
lean_inc(v_r_1669_);
lean_dec_ref_known(v_x_1666_, 5);
v___x_1670_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_1665_, v_l_1668_);
v___x_1671_ = lean_array_push(v___x_1670_, v_k_1667_);
v_init_1665_ = v___x_1671_;
v_x_1666_ = v_r_1669_;
goto _start;
}
else
{
return v_init_1665_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object* v_a_1673_, lean_object* v_a_1674_){
_start:
{
if (lean_obj_tag(v_a_1673_) == 0)
{
lean_object* v___x_1675_; 
v___x_1675_ = l_List_reverse___redArg(v_a_1674_);
return v___x_1675_;
}
else
{
lean_object* v_head_1676_; lean_object* v_tail_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1686_; 
v_head_1676_ = lean_ctor_get(v_a_1673_, 0);
v_tail_1677_ = lean_ctor_get(v_a_1673_, 1);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_a_1673_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1679_ = v_a_1673_;
v_isShared_1680_ = v_isSharedCheck_1686_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_tail_1677_);
lean_inc(v_head_1676_);
lean_dec(v_a_1673_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1686_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1681_ = l_Lean_Level_param___override(v_head_1676_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 1, v_a_1674_);
lean_ctor_set(v___x_1679_, 0, v___x_1681_);
v___x_1683_ = v___x_1679_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_a_1674_);
v___x_1683_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
v_a_1673_ = v_tail_1677_;
v_a_1674_ = v___x_1683_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object* v_x1_1687_, lean_object* v_x2_1688_){
_start:
{
lean_object* v_fst_1689_; lean_object* v_fst_1690_; uint8_t v___x_1691_; 
v_fst_1689_ = lean_ctor_get(v_x1_1687_, 0);
v_fst_1690_ = lean_ctor_get(v_x2_1688_, 0);
v___x_1691_ = l_Lean_Name_quickLt(v_fst_1689_, v_fst_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_x1_1692_, lean_object* v_x2_1693_){
_start:
{
uint8_t v_res_1694_; lean_object* v_r_1695_; 
v_res_1694_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_x1_1692_, v_x2_1693_);
lean_dec_ref(v_x2_1693_);
lean_dec_ref(v_x1_1692_);
v_r_1695_ = lean_box(v_res_1694_);
return v_r_1695_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object* v_as_1696_, lean_object* v_k_1697_, lean_object* v_x_1698_, lean_object* v_x_1699_){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v_m_1702_; lean_object* v_a_1703_; uint8_t v___x_1704_; 
v___x_1700_ = lean_nat_add(v_x_1698_, v_x_1699_);
v___x_1701_ = lean_unsigned_to_nat(1u);
v_m_1702_ = lean_nat_shiftr(v___x_1700_, v___x_1701_);
lean_dec(v___x_1700_);
v_a_1703_ = lean_array_fget_borrowed(v_as_1696_, v_m_1702_);
v___x_1704_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_a_1703_, v_k_1697_);
if (v___x_1704_ == 0)
{
uint8_t v___x_1705_; 
lean_dec(v_x_1699_);
v___x_1705_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_k_1697_, v_a_1703_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; 
lean_dec(v_m_1702_);
lean_dec(v_x_1698_);
lean_inc(v_a_1703_);
v___x_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1706_, 0, v_a_1703_);
return v___x_1706_;
}
else
{
lean_object* v___x_1707_; uint8_t v___x_1708_; lean_object* v___x_1709_; uint8_t v___y_1711_; 
v___x_1707_ = lean_unsigned_to_nat(0u);
v___x_1708_ = lean_nat_dec_eq(v_m_1702_, v___x_1707_);
v___x_1709_ = lean_nat_sub(v_m_1702_, v___x_1701_);
lean_dec(v_m_1702_);
if (v___x_1708_ == 0)
{
uint8_t v___x_1714_; 
v___x_1714_ = lean_nat_dec_lt(v___x_1709_, v_x_1698_);
v___y_1711_ = v___x_1714_;
goto v___jp_1710_;
}
else
{
v___y_1711_ = v___x_1708_;
goto v___jp_1710_;
}
v___jp_1710_:
{
if (v___y_1711_ == 0)
{
v_x_1699_ = v___x_1709_;
goto _start;
}
else
{
lean_object* v___x_1713_; 
lean_dec(v___x_1709_);
lean_dec(v_x_1698_);
v___x_1713_ = lean_box(0);
return v___x_1713_;
}
}
}
}
else
{
lean_object* v___x_1715_; uint8_t v___x_1716_; 
lean_dec(v_x_1698_);
v___x_1715_ = lean_nat_add(v_m_1702_, v___x_1701_);
lean_dec(v_m_1702_);
v___x_1716_ = lean_nat_dec_le(v___x_1715_, v_x_1699_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; 
lean_dec(v___x_1715_);
lean_dec(v_x_1699_);
v___x_1717_ = lean_box(0);
return v___x_1717_;
}
else
{
v_x_1698_ = v___x_1715_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_as_1719_, lean_object* v_k_1720_, lean_object* v_x_1721_, lean_object* v_x_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_1719_, v_k_1720_, v_x_1721_, v_x_1722_);
lean_dec_ref(v_k_1720_);
lean_dec_ref(v_as_1719_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object* v_tac_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v_env_1733_; lean_object* v___x_1734_; 
v___x_1728_ = lean_box(1);
v___x_1729_ = lean_st_ref_get(v___y_1726_);
v_env_1733_ = lean_ctor_get(v___x_1729_, 0);
lean_inc_ref(v_env_1733_);
lean_dec(v___x_1729_);
v___x_1734_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1733_, v_tac_1725_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v___x_1735_; lean_object* v_toEnvExtension_1736_; lean_object* v_asyncMode_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1735_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1736_ = lean_ctor_get(v___x_1735_, 0);
v_asyncMode_1737_ = lean_ctor_get(v_toEnvExtension_1736_, 2);
v___x_1738_ = lean_box(0);
v___x_1739_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1728_, v___x_1735_, v_env_1733_, v_asyncMode_1737_, v___x_1738_);
v___x_1740_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1739_, v_tac_1725_);
lean_dec(v_tac_1725_);
lean_dec(v___x_1739_);
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
return v___x_1741_;
}
else
{
lean_object* v_val_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1770_; 
v_val_1742_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1744_ = v___x_1734_;
v_isShared_1745_ = v_isSharedCheck_1770_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_val_1742_);
lean_dec(v___x_1734_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1770_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1746_; uint8_t v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; 
v___x_1746_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_1747_ = 0;
v___x_1748_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1728_, v___x_1746_, v_env_1733_, v_val_1742_, v___x_1747_);
lean_dec(v_val_1742_);
lean_dec_ref(v_env_1733_);
v___x_1749_ = lean_unsigned_to_nat(0u);
v___x_1750_ = lean_array_get_size(v___x_1748_);
v___x_1751_ = lean_nat_dec_lt(v___x_1749_, v___x_1750_);
if (v___x_1751_ == 0)
{
lean_dec_ref(v___x_1748_);
lean_del_object(v___x_1744_);
lean_dec(v_tac_1725_);
goto v___jp_1730_;
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1752_ = lean_unsigned_to_nat(1u);
v___x_1753_ = lean_nat_sub(v___x_1750_, v___x_1752_);
v___x_1754_ = lean_nat_dec_le(v___x_1749_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_dec(v___x_1753_);
lean_dec_ref(v___x_1748_);
lean_del_object(v___x_1744_);
lean_dec(v_tac_1725_);
goto v___jp_1730_;
}
else
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1755_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
v___x_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1756_, 0, v_tac_1725_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v___x_1748_, v___x_1756_, v___x_1749_, v___x_1753_);
lean_dec_ref_known(v___x_1756_, 2);
lean_dec_ref(v___x_1748_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_del_object(v___x_1744_);
goto v___jp_1730_;
}
else
{
lean_object* v_val_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1769_; 
v_val_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1769_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_val_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1769_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v_snd_1762_; lean_object* v___x_1764_; 
v_snd_1762_ = lean_ctor_get(v_val_1758_, 1);
lean_inc(v_snd_1762_);
lean_dec(v_val_1758_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v_snd_1762_);
v___x_1764_ = v___x_1760_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_snd_1762_);
v___x_1764_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v___x_1766_; 
if (v_isShared_1745_ == 0)
{
lean_ctor_set_tag(v___x_1744_, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1764_);
v___x_1766_ = v___x_1744_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
}
}
}
}
v___jp_1730_:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = lean_box(0);
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
return v___x_1732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object* v_tac_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_1771_, v___y_1772_);
lean_dec(v___y_1772_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object* v_t_1775_, lean_object* v_k_1776_){
_start:
{
if (lean_obj_tag(v_t_1775_) == 0)
{
lean_object* v_k_1777_; lean_object* v_v_1778_; lean_object* v_l_1779_; lean_object* v_r_1780_; uint8_t v___x_1781_; 
v_k_1777_ = lean_ctor_get(v_t_1775_, 1);
v_v_1778_ = lean_ctor_get(v_t_1775_, 2);
v_l_1779_ = lean_ctor_get(v_t_1775_, 3);
v_r_1780_ = lean_ctor_get(v_t_1775_, 4);
v___x_1781_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1776_, v_k_1777_);
switch(v___x_1781_)
{
case 0:
{
v_t_1775_ = v_l_1779_;
goto _start;
}
case 1:
{
lean_object* v___x_1783_; 
lean_inc(v_v_1778_);
v___x_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1783_, 0, v_v_1778_);
return v___x_1783_;
}
default: 
{
v_t_1775_ = v_r_1780_;
goto _start;
}
}
}
else
{
lean_object* v___x_1785_; 
v___x_1785_ = lean_box(0);
return v___x_1785_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg___boxed(lean_object* v_t_1786_, lean_object* v_k_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_1786_, v_k_1787_);
lean_dec(v_k_1787_);
lean_dec(v_t_1786_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(lean_object* v_a_1789_, lean_object* v_x_1790_){
_start:
{
if (lean_obj_tag(v_x_1790_) == 0)
{
lean_object* v___x_1791_; 
v___x_1791_ = lean_box(0);
return v___x_1791_;
}
else
{
lean_object* v_key_1792_; lean_object* v_value_1793_; lean_object* v_tail_1794_; uint8_t v___x_1795_; 
v_key_1792_ = lean_ctor_get(v_x_1790_, 0);
v_value_1793_ = lean_ctor_get(v_x_1790_, 1);
v_tail_1794_ = lean_ctor_get(v_x_1790_, 2);
v___x_1795_ = lean_name_eq(v_key_1792_, v_a_1789_);
if (v___x_1795_ == 0)
{
v_x_1790_ = v_tail_1794_;
goto _start;
}
else
{
lean_object* v___x_1797_; 
lean_inc(v_value_1793_);
v___x_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1797_, 0, v_value_1793_);
return v___x_1797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg___boxed(lean_object* v_a_1798_, lean_object* v_x_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_1798_, v_x_1799_);
lean_dec(v_x_1799_);
lean_dec(v_a_1798_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(lean_object* v_m_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v_buckets_1803_; lean_object* v___x_1804_; uint64_t v___y_1806_; 
v_buckets_1803_ = lean_ctor_get(v_m_1801_, 1);
v___x_1804_ = lean_array_get_size(v_buckets_1803_);
if (lean_obj_tag(v_a_1802_) == 0)
{
uint64_t v___x_1820_; 
v___x_1820_ = 1723ULL;
v___y_1806_ = v___x_1820_;
goto v___jp_1805_;
}
else
{
uint64_t v_hash_1821_; 
v_hash_1821_ = lean_ctor_get_uint64(v_a_1802_, sizeof(void*)*2);
v___y_1806_ = v_hash_1821_;
goto v___jp_1805_;
}
v___jp_1805_:
{
uint64_t v___x_1807_; uint64_t v___x_1808_; uint64_t v_fold_1809_; uint64_t v___x_1810_; uint64_t v___x_1811_; uint64_t v___x_1812_; size_t v___x_1813_; size_t v___x_1814_; size_t v___x_1815_; size_t v___x_1816_; size_t v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1807_ = 32ULL;
v___x_1808_ = lean_uint64_shift_right(v___y_1806_, v___x_1807_);
v_fold_1809_ = lean_uint64_xor(v___y_1806_, v___x_1808_);
v___x_1810_ = 16ULL;
v___x_1811_ = lean_uint64_shift_right(v_fold_1809_, v___x_1810_);
v___x_1812_ = lean_uint64_xor(v_fold_1809_, v___x_1811_);
v___x_1813_ = lean_uint64_to_usize(v___x_1812_);
v___x_1814_ = lean_usize_of_nat(v___x_1804_);
v___x_1815_ = ((size_t)1ULL);
v___x_1816_ = lean_usize_sub(v___x_1814_, v___x_1815_);
v___x_1817_ = lean_usize_land(v___x_1813_, v___x_1816_);
v___x_1818_ = lean_array_uget_borrowed(v_buckets_1803_, v___x_1817_);
v___x_1819_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_1802_, v___x_1818_);
return v___x_1819_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg___boxed(lean_object* v_m_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_1822_, v_a_1823_);
lean_dec(v_a_1823_);
lean_dec_ref(v_m_1822_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_keys_1825_, lean_object* v_vals_1826_, lean_object* v_i_1827_, lean_object* v_k_1828_){
_start:
{
lean_object* v___x_1829_; uint8_t v___x_1830_; 
v___x_1829_ = lean_array_get_size(v_keys_1825_);
v___x_1830_ = lean_nat_dec_lt(v_i_1827_, v___x_1829_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; 
lean_dec(v_i_1827_);
v___x_1831_ = lean_box(0);
return v___x_1831_;
}
else
{
lean_object* v_k_x27_1832_; uint8_t v___x_1833_; 
v_k_x27_1832_ = lean_array_fget_borrowed(v_keys_1825_, v_i_1827_);
v___x_1833_ = lean_name_eq(v_k_1828_, v_k_x27_1832_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = lean_unsigned_to_nat(1u);
v___x_1835_ = lean_nat_add(v_i_1827_, v___x_1834_);
lean_dec(v_i_1827_);
v_i_1827_ = v___x_1835_;
goto _start;
}
else
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = lean_array_fget_borrowed(v_vals_1826_, v_i_1827_);
lean_dec(v_i_1827_);
lean_inc(v___x_1837_);
v___x_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
return v___x_1838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object* v_keys_1839_, lean_object* v_vals_1840_, lean_object* v_i_1841_, lean_object* v_k_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_1839_, v_vals_1840_, v_i_1841_, v_k_1842_);
lean_dec(v_k_1842_);
lean_dec_ref(v_vals_1840_);
lean_dec_ref(v_keys_1839_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object* v_x_1844_, size_t v_x_1845_, lean_object* v_x_1846_){
_start:
{
if (lean_obj_tag(v_x_1844_) == 0)
{
lean_object* v_es_1847_; lean_object* v___x_1848_; size_t v___x_1849_; size_t v___x_1850_; lean_object* v_j_1851_; lean_object* v___x_1852_; 
v_es_1847_ = lean_ctor_get(v_x_1844_, 0);
v___x_1848_ = lean_box(2);
v___x_1849_ = ((size_t)31ULL);
v___x_1850_ = lean_usize_land(v_x_1845_, v___x_1849_);
v_j_1851_ = lean_usize_to_nat(v___x_1850_);
v___x_1852_ = lean_array_get_borrowed(v___x_1848_, v_es_1847_, v_j_1851_);
lean_dec(v_j_1851_);
switch(lean_obj_tag(v___x_1852_))
{
case 0:
{
lean_object* v_key_1853_; lean_object* v_val_1854_; uint8_t v___x_1855_; 
v_key_1853_ = lean_ctor_get(v___x_1852_, 0);
v_val_1854_ = lean_ctor_get(v___x_1852_, 1);
v___x_1855_ = lean_name_eq(v_x_1846_, v_key_1853_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; 
v___x_1856_ = lean_box(0);
return v___x_1856_;
}
else
{
lean_object* v___x_1857_; 
lean_inc(v_val_1854_);
v___x_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1857_, 0, v_val_1854_);
return v___x_1857_;
}
}
case 1:
{
lean_object* v_node_1858_; size_t v___x_1859_; size_t v___x_1860_; 
v_node_1858_ = lean_ctor_get(v___x_1852_, 0);
v___x_1859_ = ((size_t)5ULL);
v___x_1860_ = lean_usize_shift_right(v_x_1845_, v___x_1859_);
v_x_1844_ = v_node_1858_;
v_x_1845_ = v___x_1860_;
goto _start;
}
default: 
{
lean_object* v___x_1862_; 
v___x_1862_ = lean_box(0);
return v___x_1862_;
}
}
}
else
{
lean_object* v_ks_1863_; lean_object* v_vs_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v_ks_1863_ = lean_ctor_get(v_x_1844_, 0);
v_vs_1864_ = lean_ctor_get(v_x_1844_, 1);
v___x_1865_ = lean_unsigned_to_nat(0u);
v___x_1866_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_ks_1863_, v_vs_1864_, v___x_1865_, v_x_1846_);
return v___x_1866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_1867_, lean_object* v_x_1868_, lean_object* v_x_1869_){
_start:
{
size_t v_x_17309__boxed_1870_; lean_object* v_res_1871_; 
v_x_17309__boxed_1870_ = lean_unbox_usize(v_x_1868_);
lean_dec(v_x_1868_);
v_res_1871_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1867_, v_x_17309__boxed_1870_, v_x_1869_);
lean_dec(v_x_1869_);
lean_dec_ref(v_x_1867_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object* v_x_1872_, lean_object* v_x_1873_){
_start:
{
uint64_t v___y_1875_; 
if (lean_obj_tag(v_x_1873_) == 0)
{
uint64_t v___x_1878_; 
v___x_1878_ = 1723ULL;
v___y_1875_ = v___x_1878_;
goto v___jp_1874_;
}
else
{
uint64_t v_hash_1879_; 
v_hash_1879_ = lean_ctor_get_uint64(v_x_1873_, sizeof(void*)*2);
v___y_1875_ = v_hash_1879_;
goto v___jp_1874_;
}
v___jp_1874_:
{
size_t v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_uint64_to_usize(v___y_1875_);
v___x_1877_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1872_, v___x_1876_, v_x_1873_);
return v___x_1877_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object* v_x_1880_, lean_object* v_x_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_1880_, v_x_1881_);
lean_dec(v_x_1881_);
lean_dec_ref(v_x_1880_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object* v_x_1883_, lean_object* v_x_1884_){
_start:
{
uint8_t v_stage_u2081_1885_; 
v_stage_u2081_1885_ = lean_ctor_get_uint8(v_x_1883_, sizeof(void*)*2);
if (v_stage_u2081_1885_ == 0)
{
lean_object* v_map_u2081_1886_; lean_object* v_map_u2082_1887_; lean_object* v___x_1888_; 
v_map_u2081_1886_ = lean_ctor_get(v_x_1883_, 0);
v_map_u2082_1887_ = lean_ctor_get(v_x_1883_, 1);
v___x_1888_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_1886_, v_x_1884_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_map_u2082_1887_, v_x_1884_);
return v___x_1889_;
}
else
{
return v___x_1888_;
}
}
else
{
lean_object* v_map_u2081_1890_; lean_object* v___x_1891_; 
v_map_u2081_1890_ = lean_ctor_get(v_x_1883_, 0);
v___x_1891_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_1890_, v_x_1884_);
return v___x_1891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg___boxed(lean_object* v_x_1892_, lean_object* v_x_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_1892_, v_x_1893_);
lean_dec(v_x_1893_);
lean_dec_ref(v_x_1892_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object* v_firsts_1895_, lean_object* v_n_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1915_; lean_object* v_val_1916_; lean_object* v___x_1918_; lean_object* v___y_1920_; lean_object* v_env_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1918_ = lean_st_ref_get(v___y_1898_);
v_env_1935_ = lean_ctor_get(v___x_1918_, 0);
lean_inc_ref(v_env_1935_);
lean_dec(v___x_1918_);
v___x_1936_ = l_Lean_Environment_constants(v_env_1935_);
v___x_1937_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v___x_1936_, v_n_1896_);
lean_dec_ref(v___x_1936_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v___x_1938_; 
v___x_1938_ = lean_box(0);
v___y_1920_ = v___x_1938_;
goto v___jp_1919_;
}
else
{
lean_object* v_val_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v_val_1939_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_val_1939_);
lean_dec_ref_known(v___x_1937_, 1);
v___x_1940_ = l_Lean_ConstantInfo_levelParams(v_val_1939_);
lean_dec(v_val_1939_);
v___x_1941_ = lean_box(0);
v___x_1942_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(v___x_1940_, v___x_1941_);
v___y_1920_ = v___x_1942_;
goto v___jp_1919_;
}
v___jp_1900_:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; uint8_t v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1903_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8);
v___x_1904_ = l_Lean_Expr_const___override(v_n_1896_, v___y_1901_);
v___x_1905_ = lean_unsigned_to_nat(32u);
v___x_1906_ = lean_mk_empty_array_with_capacity(v___x_1905_);
lean_dec_ref(v___x_1906_);
v___x_1907_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1);
v___x_1908_ = lean_box(0);
v___x_1909_ = 0;
v___x_1910_ = l_Lean_MessageData_withExprHover(v___y_1902_, v___x_1904_, v___x_1907_, v___x_1908_, v___x_1908_, v___x_1908_, v___x_1909_);
v___x_1911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1903_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
lean_ctor_set(v___x_1912_, 1, v___x_1903_);
v___x_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
return v___x_1913_;
}
v___jp_1914_:
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1917_, 0, v_val_1916_);
v___y_1901_ = v___y_1915_;
v___y_1902_ = v___x_1917_;
goto v___jp_1900_;
}
v___jp_1919_:
{
lean_object* v___x_1921_; lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1934_; 
lean_inc(v_n_1896_);
v___x_1921_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_n_1896_, v___y_1898_);
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1924_ = v___x_1921_;
v_isShared_1925_ = v_isSharedCheck_1934_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1921_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1934_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
if (lean_obj_tag(v_a_1922_) == 0)
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_firsts_1895_, v_n_1896_);
if (lean_obj_tag(v___x_1926_) == 0)
{
uint8_t v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1927_ = 1;
lean_inc(v_n_1896_);
v___x_1928_ = l_Lean_Name_toString(v_n_1896_, v___x_1927_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set_tag(v___x_1924_, 3);
lean_ctor_set(v___x_1924_, 0, v___x_1928_);
v___x_1930_ = v___x_1924_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
v___y_1901_ = v___y_1920_;
v___y_1902_ = v___x_1930_;
goto v___jp_1900_;
}
}
else
{
lean_object* v_val_1932_; 
lean_del_object(v___x_1924_);
v_val_1932_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_val_1932_);
lean_dec_ref_known(v___x_1926_, 1);
v___y_1915_ = v___y_1920_;
v_val_1916_ = v_val_1932_;
goto v___jp_1914_;
}
}
else
{
lean_object* v_val_1933_; 
lean_del_object(v___x_1924_);
v_val_1933_ = lean_ctor_get(v_a_1922_, 0);
lean_inc(v_val_1933_);
lean_dec_ref_known(v_a_1922_, 1);
v___y_1915_ = v___y_1920_;
v_val_1916_ = v_val_1933_;
goto v___jp_1914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object* v_firsts_1943_, lean_object* v_n_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_firsts_1943_, v_n_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v_firsts_1943_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object* v_a_1949_, lean_object* v_x_1950_, lean_object* v_x_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
if (lean_obj_tag(v_x_1950_) == 0)
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = l_List_reverse___redArg(v_x_1951_);
v___x_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1955_);
return v___x_1956_;
}
else
{
lean_object* v_head_1957_; lean_object* v_tail_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1976_; 
v_head_1957_ = lean_ctor_get(v_x_1950_, 0);
v_tail_1958_ = lean_ctor_get(v_x_1950_, 1);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_x_1950_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1960_ = v_x_1950_;
v_isShared_1961_ = v_isSharedCheck_1976_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_tail_1958_);
lean_inc(v_head_1957_);
lean_dec(v_x_1950_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1976_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1962_; 
v___x_1962_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_a_1949_, v_head_1957_, v___y_1952_, v___y_1953_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1965_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___x_1962_, 1);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 1, v_x_1951_);
lean_ctor_set(v___x_1960_, 0, v_a_1963_);
v___x_1965_ = v___x_1960_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1963_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_x_1951_);
v___x_1965_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
v_x_1950_ = v_tail_1958_;
v_x_1951_ = v___x_1965_;
goto _start;
}
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
lean_del_object(v___x_1960_);
lean_dec(v_tail_1958_);
lean_dec(v_x_1951_);
v_a_1968_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1962_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1962_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object* v_a_1977_, lean_object* v_x_1978_, lean_object* v_x_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_1977_, v_x_1978_, v_x_1979_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v_a_1977_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object* v_val_1984_, lean_object* v___x_1985_, lean_object* v___x_1986_, lean_object* v_a_1987_, lean_object* v_b_1988_){
_start:
{
lean_object* v_it_1990_; lean_object* v_startInclusive_1991_; lean_object* v_endExclusive_1992_; 
if (lean_obj_tag(v_a_1987_) == 0)
{
lean_object* v_currPos_1997_; lean_object* v_searcher_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2021_; 
v_currPos_1997_ = lean_ctor_get(v_a_1987_, 0);
v_searcher_1998_ = lean_ctor_get(v_a_1987_, 1);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_a_1987_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2000_ = v_a_1987_;
v_isShared_2001_ = v_isSharedCheck_2021_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_searcher_1998_);
lean_inc(v_currPos_1997_);
lean_dec(v_a_1987_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2021_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
uint8_t v_decide_2002_; 
v_decide_2002_ = lean_nat_dec_eq(v_searcher_1998_, v___x_1986_);
if (v_decide_2002_ == 0)
{
uint32_t v___x_2003_; uint32_t v___x_2004_; uint8_t v___x_2005_; 
v___x_2003_ = 10;
v___x_2004_ = lean_string_utf8_get_fast(v_val_1984_, v_searcher_1998_);
v___x_2005_ = lean_uint32_dec_eq(v___x_2004_, v___x_2003_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; lean_object* v___x_2008_; 
v___x_2006_ = lean_string_utf8_next_fast(v_val_1984_, v_searcher_1998_);
lean_dec(v_searcher_1998_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 1, v___x_2006_);
v___x_2008_ = v___x_2000_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_currPos_1997_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
v_a_1987_ = v___x_2008_;
goto _start;
}
}
else
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v_slice_2014_; lean_object* v_nextIt_2016_; 
v___x_2011_ = lean_string_utf8_next_fast(v_val_1984_, v_searcher_1998_);
v___x_2012_ = lean_nat_sub(v___x_2011_, v_searcher_1998_);
v___x_2013_ = lean_nat_add(v_searcher_1998_, v___x_2012_);
lean_dec(v___x_2012_);
v_slice_2014_ = l_String_Slice_subslice_x21(v___x_1985_, v_currPos_1997_, v_searcher_1998_);
lean_inc(v___x_2013_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 1, v___x_2013_);
lean_ctor_set(v___x_2000_, 0, v___x_2013_);
v_nextIt_2016_ = v___x_2000_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v___x_2013_);
v_nextIt_2016_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v_startInclusive_2017_; lean_object* v_endExclusive_2018_; 
v_startInclusive_2017_ = lean_ctor_get(v_slice_2014_, 0);
lean_inc(v_startInclusive_2017_);
v_endExclusive_2018_ = lean_ctor_get(v_slice_2014_, 1);
lean_inc(v_endExclusive_2018_);
lean_dec_ref(v_slice_2014_);
v_it_1990_ = v_nextIt_2016_;
v_startInclusive_1991_ = v_startInclusive_2017_;
v_endExclusive_1992_ = v_endExclusive_2018_;
goto v___jp_1989_;
}
}
}
else
{
lean_object* v___x_2020_; 
lean_del_object(v___x_2000_);
lean_dec(v_searcher_1998_);
v___x_2020_ = lean_box(1);
lean_inc(v___x_1986_);
v_it_1990_ = v___x_2020_;
v_startInclusive_1991_ = v_currPos_1997_;
v_endExclusive_1992_ = v___x_1986_;
goto v___jp_1989_;
}
}
}
else
{
lean_dec(v___x_1986_);
return v_b_1988_;
}
v___jp_1989_:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1993_ = lean_string_utf8_extract_fast(v_val_1984_, v_startInclusive_1991_, v_endExclusive_1992_);
lean_dec(v_endExclusive_1992_);
lean_dec(v_startInclusive_1991_);
v___x_1994_ = l_Lean_stringToMessageData(v___x_1993_);
v___x_1995_ = lean_array_push(v_b_1988_, v___x_1994_);
v_a_1987_ = v_it_1990_;
v_b_1988_ = v___x_1995_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object* v_val_2022_, lean_object* v___x_2023_, lean_object* v___x_2024_, lean_object* v_a_2025_, lean_object* v_b_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2022_, v___x_2023_, v___x_2024_, v_a_2025_, v_b_2026_);
lean_dec_ref(v___x_2023_);
lean_dec_ref(v_val_2022_);
return v_res_2027_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2(void){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1));
v___x_2032_ = l_Lean_stringToMessageData(v___x_2031_);
return v___x_2032_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4(void){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3));
v___x_2035_ = l_Lean_stringToMessageData(v___x_2034_);
return v___x_2035_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6(void){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5));
v___x_2038_ = l_Lean_stringToMessageData(v___x_2037_);
return v___x_2038_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9(void){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8));
v___x_2043_ = l_Lean_MessageData_ofFormat(v___x_2042_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_x_2046_, lean_object* v_x_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
if (lean_obj_tag(v_x_2046_) == 0)
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = l_List_reverse___redArg(v_x_2047_);
v___x_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
return v___x_2052_;
}
else
{
lean_object* v_head_2053_; lean_object* v_tail_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2151_; 
v_head_2053_ = lean_ctor_get(v_x_2046_, 0);
v_tail_2054_ = lean_ctor_get(v_x_2046_, 1);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_x_2046_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2056_ = v_x_2046_;
v_isShared_2057_ = v_isSharedCheck_2151_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_tail_2054_);
lean_inc(v_head_2053_);
lean_dec(v_x_2046_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2151_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v_snd_2071_; lean_object* v_fst_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2150_; 
v_snd_2071_ = lean_ctor_get(v_head_2053_, 1);
v_fst_2072_ = lean_ctor_get(v_head_2053_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_head_2053_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2074_ = v_head_2053_;
v_isShared_2075_ = v_isSharedCheck_2150_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_snd_2071_);
lean_inc(v_fst_2072_);
lean_dec(v_head_2053_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2150_;
goto v_resetjp_2073_;
}
v___jp_2058_:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2068_; 
v___x_2063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___y_2061_);
lean_ctor_set(v___x_2063_, 1, v___y_2062_);
v___x_2064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
lean_ctor_set(v___x_2064_, 1, v___y_2060_);
v___x_2065_ = l_Lean_MessageData_nestD(v___x_2064_);
lean_inc_ref(v___y_2059_);
v___x_2066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___y_2059_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 1, v_x_2047_);
lean_ctor_set(v___x_2056_, 0, v___x_2066_);
v___x_2068_ = v___x_2056_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2066_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v_x_2047_);
v___x_2068_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
v_x_2046_ = v_tail_2054_;
v_x_2047_ = v___x_2068_;
goto _start;
}
}
v_resetjp_2073_:
{
lean_object* v_fst_2076_; lean_object* v_snd_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2149_; 
v_fst_2076_ = lean_ctor_get(v_snd_2071_, 0);
v_snd_2077_ = lean_ctor_get(v_snd_2071_, 1);
v_isSharedCheck_2149_ = !lean_is_exclusive(v_snd_2071_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2079_ = v_snd_2071_;
v_isShared_2080_ = v_isSharedCheck_2149_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_snd_2077_);
lean_inc(v_fst_2076_);
lean_dec(v_snd_2071_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2149_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v_a_2104_; lean_object* v___y_2120_; lean_object* v___x_2129_; 
v___x_2129_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2045_, v_fst_2072_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v___x_2130_; 
v___x_2130_ = l_Lean_MessageData_nil;
v_a_2104_ = v___x_2130_;
goto v___jp_2103_;
}
else
{
lean_object* v_val_2131_; 
v_val_2131_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_val_2131_);
lean_dec_ref_known(v___x_2129_, 1);
if (lean_obj_tag(v_val_2131_) == 0)
{
lean_object* v_size_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___x_2140_; uint8_t v___x_2141_; 
v_size_2132_ = lean_ctor_get(v_val_2131_, 0);
v___x_2133_ = lean_mk_empty_array_with_capacity(v_size_2132_);
v___x_2134_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v___x_2133_, v_val_2131_);
v___x_2135_ = lean_array_get_size(v___x_2134_);
v___x_2140_ = lean_unsigned_to_nat(0u);
v___x_2141_ = lean_nat_dec_eq(v___x_2135_, v___x_2140_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___y_2145_; uint8_t v___x_2147_; 
v___x_2142_ = lean_unsigned_to_nat(1u);
v___x_2143_ = lean_nat_sub(v___x_2135_, v___x_2142_);
v___x_2147_ = lean_nat_dec_le(v___x_2140_, v___x_2143_);
if (v___x_2147_ == 0)
{
lean_inc(v___x_2143_);
v___y_2145_ = v___x_2143_;
goto v___jp_2144_;
}
else
{
v___y_2145_ = v___x_2140_;
goto v___jp_2144_;
}
v___jp_2144_:
{
uint8_t v___x_2146_; 
v___x_2146_ = lean_nat_dec_le(v___y_2145_, v___x_2143_);
if (v___x_2146_ == 0)
{
lean_dec(v___x_2143_);
lean_inc(v___y_2145_);
v___y_2137_ = v___y_2145_;
v___y_2138_ = v___y_2145_;
goto v___jp_2136_;
}
else
{
v___y_2137_ = v___y_2145_;
v___y_2138_ = v___x_2143_;
goto v___jp_2136_;
}
}
}
else
{
v___y_2120_ = v___x_2134_;
goto v___jp_2119_;
}
v___jp_2136_:
{
lean_object* v___x_2139_; 
v___x_2139_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v___x_2135_, v___x_2134_, v___y_2137_, v___y_2138_);
lean_dec(v___y_2138_);
v___y_2120_ = v___x_2139_;
goto v___jp_2119_;
}
}
else
{
lean_object* v___x_2148_; 
v___x_2148_ = l_Lean_MessageData_nil;
v_a_2104_ = v___x_2148_;
goto v___jp_2103_;
}
}
v___jp_2081_:
{
lean_object* v___x_2087_; 
if (v_isShared_2080_ == 0)
{
lean_ctor_set_tag(v___x_2079_, 7);
lean_ctor_set(v___x_2079_, 1, v___y_2085_);
lean_ctor_set(v___x_2079_, 0, v___y_2084_);
v___x_2087_ = v___x_2079_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___y_2084_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v___y_2085_);
v___x_2087_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
if (lean_obj_tag(v_snd_2077_) == 0)
{
lean_object* v___x_2088_; 
lean_del_object(v___x_2074_);
v___x_2088_ = l_Lean_MessageData_nil;
v___y_2059_ = v___y_2083_;
v___y_2060_ = v___y_2082_;
v___y_2061_ = v___x_2087_;
v___y_2062_ = v___x_2088_;
goto v___jp_2058_;
}
else
{
lean_object* v_val_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2100_; 
v_val_2089_ = lean_ctor_get(v_snd_2077_, 0);
lean_inc_n(v_val_2089_, 2);
lean_dec_ref_known(v_snd_2077_, 1);
v___x_2090_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2091_ = lean_unsigned_to_nat(0u);
v___x_2092_ = lean_string_utf8_byte_size(v_val_2089_);
v___x_2093_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2093_, 0, v_val_2089_);
lean_ctor_set(v___x_2093_, 1, v___x_2091_);
lean_ctor_set(v___x_2093_, 2, v___x_2092_);
v___x_2094_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0);
v___x_2095_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0));
v___x_2096_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2089_, v___x_2093_, v___x_2092_, v___x_2094_, v___x_2095_);
lean_dec_ref_known(v___x_2093_, 3);
lean_dec(v_val_2089_);
v___x_2097_ = lean_array_to_list(v___x_2096_);
v___x_2098_ = l_Lean_MessageData_joinSep(v___x_2097_, v___x_2090_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set_tag(v___x_2074_, 7);
lean_ctor_set(v___x_2074_, 1, v___x_2098_);
lean_ctor_set(v___x_2074_, 0, v___x_2090_);
v___x_2100_ = v___x_2074_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2090_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
v___y_2059_ = v___y_2083_;
v___y_2060_ = v___y_2082_;
v___y_2061_ = v___x_2087_;
v___y_2062_ = v___x_2100_;
goto v___jp_2058_;
}
}
}
}
v___jp_2103_:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; lean_object* v___x_2111_; uint8_t v___x_2112_; 
v___x_2105_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2);
v___x_2106_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8);
lean_inc(v_fst_2072_);
v___x_2107_ = l_Lean_MessageData_ofName(v_fst_2072_);
v___x_2108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2106_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
v___x_2109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
lean_ctor_set(v___x_2109_, 1, v___x_2106_);
v___x_2110_ = 1;
v___x_2111_ = l_Lean_Name_toString(v_fst_2072_, v___x_2110_);
v___x_2112_ = lean_string_dec_eq(v___x_2111_, v_fst_2076_);
lean_dec_ref(v___x_2111_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2113_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4);
v___x_2114_ = l_Lean_stringToMessageData(v_fst_2076_);
v___x_2115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2113_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
v___x_2116_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6);
v___x_2117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2115_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
v___y_2082_ = v_a_2104_;
v___y_2083_ = v___x_2105_;
v___y_2084_ = v___x_2109_;
v___y_2085_ = v___x_2117_;
goto v___jp_2081_;
}
else
{
lean_object* v___x_2118_; 
lean_dec(v_fst_2076_);
v___x_2118_ = l_Lean_MessageData_nil;
v___y_2082_ = v_a_2104_;
v___y_2083_ = v___x_2105_;
v___y_2084_ = v___x_2109_;
v___y_2085_ = v___x_2118_;
goto v___jp_2081_;
}
}
v___jp_2119_:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2121_ = lean_array_to_list(v___y_2120_);
v___x_2122_ = lean_box(0);
v___x_2123_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_2044_, v___x_2121_, v___x_2122_, v___y_2048_, v___y_2049_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2123_, 1);
v___x_2125_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2126_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9);
v___x_2127_ = l_Lean_MessageData_joinSep(v_a_2124_, v___x_2126_);
v___x_2128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2125_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v_a_2104_ = v___x_2128_;
goto v___jp_2103_;
}
else
{
lean_del_object(v___x_2079_);
lean_dec(v_snd_2077_);
lean_dec(v_fst_2076_);
lean_del_object(v___x_2074_);
lean_dec(v_fst_2072_);
lean_del_object(v___x_2056_);
lean_dec(v_tail_2054_);
lean_dec(v_x_2047_);
return v___x_2123_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_x_2154_, lean_object* v_x_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_2152_, v_a_2153_, v_x_2154_, v_x_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v_a_2153_);
lean_dec(v_a_2152_);
return v_res_2159_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(uint8_t v_suppressElabErrors_2161_, uint8_t v___y_2162_, lean_object* v_x_2163_){
_start:
{
if (lean_obj_tag(v_x_2163_) == 1)
{
lean_object* v_pre_2164_; 
v_pre_2164_ = lean_ctor_get(v_x_2163_, 0);
if (lean_obj_tag(v_pre_2164_) == 0)
{
lean_object* v_str_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; 
v_str_2165_ = lean_ctor_get(v_x_2163_, 1);
v___x_2166_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0));
v___x_2167_ = lean_string_dec_eq(v_str_2165_, v___x_2166_);
if (v___x_2167_ == 0)
{
return v___x_2167_;
}
else
{
return v_suppressElabErrors_2161_;
}
}
else
{
return v___y_2162_;
}
}
else
{
return v___y_2162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed(lean_object* v_suppressElabErrors_2168_, lean_object* v___y_2169_, lean_object* v_x_2170_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2171_; uint8_t v___y_17925__boxed_2172_; uint8_t v_res_2173_; lean_object* v_r_2174_; 
v_suppressElabErrors_boxed_2171_ = lean_unbox(v_suppressElabErrors_2168_);
v___y_17925__boxed_2172_ = lean_unbox(v___y_2169_);
v_res_2173_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(v_suppressElabErrors_boxed_2171_, v___y_17925__boxed_2172_, v_x_2170_);
lean_dec(v_x_2170_);
v_r_2174_ = lean_box(v_res_2173_);
return v_r_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(lean_object* v_ref_2175_, lean_object* v_msgData_2176_, uint8_t v_severity_2177_, uint8_t v_isSilent_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; uint8_t v___y_2187_; lean_object* v___y_2188_; uint8_t v___y_2189_; lean_object* v___y_2190_; uint8_t v___y_2248_; uint8_t v___y_2249_; uint8_t v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; uint8_t v___y_2276_; uint8_t v___y_2277_; lean_object* v___y_2278_; uint8_t v___y_2279_; lean_object* v___y_2280_; uint8_t v___y_2284_; uint8_t v___y_2285_; uint8_t v___y_2286_; uint8_t v___x_2301_; uint8_t v___y_2303_; uint8_t v___y_2304_; uint8_t v___y_2305_; uint8_t v___y_2307_; uint8_t v___x_2319_; 
v___x_2301_ = 2;
v___x_2319_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2177_, v___x_2301_);
if (v___x_2319_ == 0)
{
v___y_2307_ = v___x_2319_;
goto v___jp_2306_;
}
else
{
uint8_t v___x_2320_; 
lean_inc_ref(v_msgData_2176_);
v___x_2320_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2176_);
v___y_2307_ = v___x_2320_;
goto v___jp_2306_;
}
v___jp_2182_:
{
lean_object* v___x_2191_; 
v___x_2191_ = l_Lean_Elab_Command_getScope___redArg(v___y_2190_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v_currNamespace_2193_; lean_object* v___x_2194_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_a_2192_);
lean_dec_ref_known(v___x_2191_, 1);
v_currNamespace_2193_ = lean_ctor_get(v_a_2192_, 2);
lean_inc(v_currNamespace_2193_);
lean_dec(v_a_2192_);
v___x_2194_ = l_Lean_Elab_Command_getScope___redArg(v___y_2190_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2230_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2197_ = v___x_2194_;
v_isShared_2198_ = v_isSharedCheck_2230_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2194_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2230_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v_openDecls_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v_env_2204_; lean_object* v_messages_2205_; lean_object* v_scopes_2206_; lean_object* v_usedQuotCtxts_2207_; lean_object* v_nextMacroScope_2208_; lean_object* v_maxRecDepth_2209_; lean_object* v_ngen_2210_; lean_object* v_auxDeclNGen_2211_; lean_object* v_infoState_2212_; lean_object* v_traceState_2213_; lean_object* v_snapshotTasks_2214_; lean_object* v_prevLinterStates_2215_; lean_object* v_codeQualityEntryTasks_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2229_; 
v_openDecls_2199_ = lean_ctor_get(v_a_2195_, 3);
lean_inc(v_openDecls_2199_);
lean_dec(v_a_2195_);
v___x_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2200_, 0, v_currNamespace_2193_);
lean_ctor_set(v___x_2200_, 1, v_openDecls_2199_);
v___x_2201_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
lean_ctor_set(v___x_2201_, 1, v___y_2184_);
lean_inc_ref(v___y_2185_);
lean_inc_ref(v___y_2186_);
v___x_2202_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2202_, 0, v___y_2186_);
lean_ctor_set(v___x_2202_, 1, v___y_2188_);
lean_ctor_set(v___x_2202_, 2, v___y_2183_);
lean_ctor_set(v___x_2202_, 3, v___y_2185_);
lean_ctor_set(v___x_2202_, 4, v___x_2201_);
lean_ctor_set_uint8(v___x_2202_, sizeof(void*)*5, v___y_2189_);
lean_ctor_set_uint8(v___x_2202_, sizeof(void*)*5 + 1, v___y_2187_);
lean_ctor_set_uint8(v___x_2202_, sizeof(void*)*5 + 2, v_isSilent_2178_);
v___x_2203_ = lean_st_ref_take(v___y_2190_);
v_env_2204_ = lean_ctor_get(v___x_2203_, 0);
v_messages_2205_ = lean_ctor_get(v___x_2203_, 1);
v_scopes_2206_ = lean_ctor_get(v___x_2203_, 2);
v_usedQuotCtxts_2207_ = lean_ctor_get(v___x_2203_, 3);
v_nextMacroScope_2208_ = lean_ctor_get(v___x_2203_, 4);
v_maxRecDepth_2209_ = lean_ctor_get(v___x_2203_, 5);
v_ngen_2210_ = lean_ctor_get(v___x_2203_, 6);
v_auxDeclNGen_2211_ = lean_ctor_get(v___x_2203_, 7);
v_infoState_2212_ = lean_ctor_get(v___x_2203_, 8);
v_traceState_2213_ = lean_ctor_get(v___x_2203_, 9);
v_snapshotTasks_2214_ = lean_ctor_get(v___x_2203_, 10);
v_prevLinterStates_2215_ = lean_ctor_get(v___x_2203_, 11);
v_codeQualityEntryTasks_2216_ = lean_ctor_get(v___x_2203_, 12);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2218_ = v___x_2203_;
v_isShared_2219_ = v_isSharedCheck_2229_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2216_);
lean_inc(v_prevLinterStates_2215_);
lean_inc(v_snapshotTasks_2214_);
lean_inc(v_traceState_2213_);
lean_inc(v_infoState_2212_);
lean_inc(v_auxDeclNGen_2211_);
lean_inc(v_ngen_2210_);
lean_inc(v_maxRecDepth_2209_);
lean_inc(v_nextMacroScope_2208_);
lean_inc(v_usedQuotCtxts_2207_);
lean_inc(v_scopes_2206_);
lean_inc(v_messages_2205_);
lean_inc(v_env_2204_);
lean_dec(v___x_2203_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2229_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2223_; 
v___x_2220_ = lean_box(0);
v___x_2221_ = l_Lean_MessageLog_add(v___x_2202_, v_messages_2205_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v___x_2221_);
v___x_2223_ = v___x_2218_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_env_2204_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v___x_2221_);
lean_ctor_set(v_reuseFailAlloc_2228_, 2, v_scopes_2206_);
lean_ctor_set(v_reuseFailAlloc_2228_, 3, v_usedQuotCtxts_2207_);
lean_ctor_set(v_reuseFailAlloc_2228_, 4, v_nextMacroScope_2208_);
lean_ctor_set(v_reuseFailAlloc_2228_, 5, v_maxRecDepth_2209_);
lean_ctor_set(v_reuseFailAlloc_2228_, 6, v_ngen_2210_);
lean_ctor_set(v_reuseFailAlloc_2228_, 7, v_auxDeclNGen_2211_);
lean_ctor_set(v_reuseFailAlloc_2228_, 8, v_infoState_2212_);
lean_ctor_set(v_reuseFailAlloc_2228_, 9, v_traceState_2213_);
lean_ctor_set(v_reuseFailAlloc_2228_, 10, v_snapshotTasks_2214_);
lean_ctor_set(v_reuseFailAlloc_2228_, 11, v_prevLinterStates_2215_);
lean_ctor_set(v_reuseFailAlloc_2228_, 12, v_codeQualityEntryTasks_2216_);
v___x_2223_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
lean_object* v___x_2224_; lean_object* v___x_2226_; 
v___x_2224_ = lean_st_ref_put(v___y_2190_, v___x_2223_);
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 0, v___x_2220_);
v___x_2226_ = v___x_2197_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2220_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec(v_currNamespace_2193_);
lean_dec_ref(v___y_2188_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
v_a_2231_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2194_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2194_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec_ref(v___y_2188_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
v_a_2239_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2191_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2191_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
v___jp_2247_:
{
lean_object* v_fileName_2253_; lean_object* v_fileMap_2254_; uint8_t v_suppressElabErrors_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___f_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2274_; 
v_fileName_2253_ = lean_ctor_get(v___y_2179_, 0);
v_fileMap_2254_ = lean_ctor_get(v___y_2179_, 1);
v_suppressElabErrors_2255_ = lean_ctor_get_uint8(v___y_2179_, sizeof(void*)*10);
v___x_2256_ = lean_box(v_suppressElabErrors_2255_);
v___x_2257_ = lean_box(v___y_2248_);
v___f_2258_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2258_, 0, v___x_2256_);
lean_closure_set(v___f_2258_, 1, v___x_2257_);
v___x_2259_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2176_);
v___x_2260_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v___x_2259_, v___y_2180_);
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2263_ = v___x_2260_;
v_isShared_2264_ = v_isSharedCheck_2274_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2260_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2274_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
lean_inc_ref_n(v_fileMap_2254_, 2);
v___x_2265_ = l_Lean_FileMap_toPosition(v_fileMap_2254_, v___y_2251_);
lean_dec(v___y_2251_);
v___x_2266_ = l_Lean_FileMap_toPosition(v_fileMap_2254_, v___y_2252_);
lean_dec(v___y_2252_);
v___x_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
v___x_2268_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
if (v_suppressElabErrors_2255_ == 0)
{
lean_del_object(v___x_2263_);
lean_dec_ref(v___f_2258_);
v___y_2183_ = v___x_2267_;
v___y_2184_ = v_a_2261_;
v___y_2185_ = v___x_2268_;
v___y_2186_ = v_fileName_2253_;
v___y_2187_ = v___y_2249_;
v___y_2188_ = v___x_2265_;
v___y_2189_ = v___y_2250_;
v___y_2190_ = v___y_2180_;
goto v___jp_2182_;
}
else
{
uint8_t v___x_2269_; 
lean_inc(v_a_2261_);
v___x_2269_ = l_Lean_MessageData_hasTag(v___f_2258_, v_a_2261_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2270_; lean_object* v___x_2272_; 
lean_dec_ref_known(v___x_2267_, 1);
lean_dec_ref(v___x_2265_);
lean_dec(v_a_2261_);
v___x_2270_ = lean_box(0);
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 0, v___x_2270_);
v___x_2272_ = v___x_2263_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
else
{
lean_del_object(v___x_2263_);
v___y_2183_ = v___x_2267_;
v___y_2184_ = v_a_2261_;
v___y_2185_ = v___x_2268_;
v___y_2186_ = v_fileName_2253_;
v___y_2187_ = v___y_2249_;
v___y_2188_ = v___x_2265_;
v___y_2189_ = v___y_2250_;
v___y_2190_ = v___y_2180_;
goto v___jp_2182_;
}
}
}
}
v___jp_2275_:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_Syntax_getTailPos_x3f(v___y_2278_, v___y_2279_);
lean_dec(v___y_2278_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_inc(v___y_2280_);
v___y_2248_ = v___y_2276_;
v___y_2249_ = v___y_2277_;
v___y_2250_ = v___y_2279_;
v___y_2251_ = v___y_2280_;
v___y_2252_ = v___y_2280_;
goto v___jp_2247_;
}
else
{
lean_object* v_val_2282_; 
v_val_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_val_2282_);
lean_dec_ref_known(v___x_2281_, 1);
v___y_2248_ = v___y_2276_;
v___y_2249_ = v___y_2277_;
v___y_2250_ = v___y_2279_;
v___y_2251_ = v___y_2280_;
v___y_2252_ = v_val_2282_;
goto v___jp_2247_;
}
}
v___jp_2283_:
{
lean_object* v___x_2287_; 
v___x_2287_ = l_Lean_Elab_Command_getRef___redArg(v___y_2179_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v_ref_2289_; lean_object* v___x_2290_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___x_2287_, 1);
v_ref_2289_ = l_Lean_replaceRef(v_ref_2175_, v_a_2288_);
lean_dec(v_a_2288_);
v___x_2290_ = l_Lean_Syntax_getPos_x3f(v_ref_2289_, v___y_2285_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v___x_2291_; 
v___x_2291_ = lean_unsigned_to_nat(0u);
v___y_2276_ = v___y_2284_;
v___y_2277_ = v___y_2286_;
v___y_2278_ = v_ref_2289_;
v___y_2279_ = v___y_2285_;
v___y_2280_ = v___x_2291_;
goto v___jp_2275_;
}
else
{
lean_object* v_val_2292_; 
v_val_2292_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_val_2292_);
lean_dec_ref_known(v___x_2290_, 1);
v___y_2276_ = v___y_2284_;
v___y_2277_ = v___y_2286_;
v___y_2278_ = v_ref_2289_;
v___y_2279_ = v___y_2285_;
v___y_2280_ = v_val_2292_;
goto v___jp_2275_;
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_dec_ref(v_msgData_2176_);
v_a_2293_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2287_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2287_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
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
v___jp_2302_:
{
if (v___y_2305_ == 0)
{
v___y_2284_ = v___y_2303_;
v___y_2285_ = v___y_2304_;
v___y_2286_ = v_severity_2177_;
goto v___jp_2283_;
}
else
{
v___y_2284_ = v___y_2303_;
v___y_2285_ = v___y_2304_;
v___y_2286_ = v___x_2301_;
goto v___jp_2283_;
}
}
v___jp_2306_:
{
if (v___y_2307_ == 0)
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v_scopes_2310_; lean_object* v___x_2311_; lean_object* v_opts_2312_; uint8_t v___x_2313_; uint8_t v___x_2314_; 
v___x_2308_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2309_ = lean_st_ref_get(v___y_2180_);
v_scopes_2310_ = lean_ctor_get(v___x_2309_, 2);
lean_inc(v_scopes_2310_);
lean_dec(v___x_2309_);
v___x_2311_ = l_List_head_x21___redArg(v___x_2308_, v_scopes_2310_);
lean_dec(v_scopes_2310_);
v_opts_2312_ = lean_ctor_get(v___x_2311_, 1);
lean_inc_ref(v_opts_2312_);
lean_dec(v___x_2311_);
v___x_2313_ = 1;
v___x_2314_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2177_, v___x_2313_);
if (v___x_2314_ == 0)
{
lean_dec_ref(v_opts_2312_);
v___y_2303_ = v___y_2307_;
v___y_2304_ = v___y_2307_;
v___y_2305_ = v___x_2314_;
goto v___jp_2302_;
}
else
{
lean_object* v___x_2315_; uint8_t v___x_2316_; 
v___x_2315_ = l_Lean_warningAsError;
v___x_2316_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_2312_, v___x_2315_);
lean_dec_ref(v_opts_2312_);
v___y_2303_ = v___y_2307_;
v___y_2304_ = v___y_2307_;
v___y_2305_ = v___x_2316_;
goto v___jp_2302_;
}
}
else
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
lean_dec_ref(v_msgData_2176_);
v___x_2317_ = lean_box(0);
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
return v___x_2318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___boxed(lean_object* v_ref_2321_, lean_object* v_msgData_2322_, lean_object* v_severity_2323_, lean_object* v_isSilent_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
uint8_t v_severity_boxed_2328_; uint8_t v_isSilent_boxed_2329_; lean_object* v_res_2330_; 
v_severity_boxed_2328_ = lean_unbox(v_severity_2323_);
v_isSilent_boxed_2329_ = lean_unbox(v_isSilent_2324_);
v_res_2330_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_ref_2321_, v_msgData_2322_, v_severity_boxed_2328_, v_isSilent_boxed_2329_, v___y_2325_, v___y_2326_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v_ref_2321_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(lean_object* v_msgData_2331_, uint8_t v_severity_2332_, uint8_t v_isSilent_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_Elab_Command_getRef___redArg(v___y_2334_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2339_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v___x_2339_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_a_2338_, v_msgData_2331_, v_severity_2332_, v_isSilent_2333_, v___y_2334_, v___y_2335_);
lean_dec(v_a_2338_);
return v___x_2339_;
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec_ref(v_msgData_2331_);
v_a_2340_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2337_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2337_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26___boxed(lean_object* v_msgData_2348_, lean_object* v_severity_2349_, lean_object* v_isSilent_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
uint8_t v_severity_boxed_2354_; uint8_t v_isSilent_boxed_2355_; lean_object* v_res_2356_; 
v_severity_boxed_2354_ = lean_unbox(v_severity_2349_);
v_isSilent_boxed_2355_ = lean_unbox(v_isSilent_2350_);
v_res_2356_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_2348_, v_severity_boxed_2354_, v_isSilent_boxed_2355_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object* v_msgData_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
uint8_t v___x_2361_; uint8_t v___x_2362_; lean_object* v___x_2363_; 
v___x_2361_ = 0;
v___x_2362_ = 0;
v___x_2363_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_2357_, v___x_2361_, v___x_2362_, v___y_2358_, v___y_2359_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object* v_msgData_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v_msgData_2364_, v___y_2365_, v___y_2366_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object* v_init_2369_, lean_object* v_x_2370_){
_start:
{
if (lean_obj_tag(v_x_2370_) == 0)
{
lean_object* v_k_2372_; lean_object* v_v_2373_; lean_object* v_l_2374_; lean_object* v_r_2375_; lean_object* v___x_2376_; lean_object* v_a_2377_; lean_object* v_a_2378_; lean_object* v___x_2379_; 
v_k_2372_ = lean_ctor_get(v_x_2370_, 1);
lean_inc(v_k_2372_);
v_v_2373_ = lean_ctor_get(v_x_2370_, 2);
lean_inc(v_v_2373_);
v_l_2374_ = lean_ctor_get(v_x_2370_, 3);
lean_inc(v_l_2374_);
v_r_2375_ = lean_ctor_get(v_x_2370_, 4);
lean_inc(v_r_2375_);
lean_dec_ref_known(v_x_2370_, 5);
v___x_2376_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_2369_, v_l_2374_);
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2377_);
lean_dec_ref(v___x_2376_);
v_a_2378_ = lean_ctor_get(v_a_2377_, 0);
lean_inc(v_a_2378_);
lean_dec(v_a_2377_);
v___x_2379_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2372_, v_v_2373_, v_a_2378_);
v_init_2369_ = v___x_2379_;
v_x_2370_ = v_r_2375_;
goto _start;
}
else
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2381_, 0, v_init_2369_);
v___x_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
return v___x_2382_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object* v_init_2383_, lean_object* v_x_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_2383_, v_x_2384_);
return v_res_2386_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(uint8_t v___x_2387_, lean_object* v_x1_2388_, lean_object* v_x2_2389_){
_start:
{
lean_object* v_fst_2390_; lean_object* v_fst_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; uint8_t v___x_2394_; 
v_fst_2390_ = lean_ctor_get(v_x1_2388_, 0);
lean_inc(v_fst_2390_);
lean_dec_ref(v_x1_2388_);
v_fst_2391_ = lean_ctor_get(v_x2_2389_, 0);
lean_inc(v_fst_2391_);
lean_dec_ref(v_x2_2389_);
v___x_2392_ = l_Lean_Name_toString(v_fst_2390_, v___x_2387_);
v___x_2393_ = l_Lean_Name_toString(v_fst_2391_, v___x_2387_);
v___x_2394_ = lean_string_dec_lt(v___x_2392_, v___x_2393_);
lean_dec_ref(v___x_2393_);
lean_dec_ref(v___x_2392_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0___boxed(lean_object* v___x_2395_, lean_object* v_x1_2396_, lean_object* v_x2_2397_){
_start:
{
uint8_t v___x_18268__boxed_2398_; uint8_t v_res_2399_; lean_object* v_r_2400_; 
v___x_18268__boxed_2398_ = lean_unbox(v___x_2395_);
v_res_2399_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_18268__boxed_2398_, v_x1_2396_, v_x2_2397_);
v_r_2400_ = lean_box(v_res_2399_);
return v_r_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(lean_object* v_hi_2401_, lean_object* v_pivot_2402_, lean_object* v_as_2403_, lean_object* v_i_2404_, lean_object* v_k_2405_){
_start:
{
uint8_t v___x_2406_; 
v___x_2406_ = lean_nat_dec_lt(v_k_2405_, v_hi_2401_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
lean_dec(v_k_2405_);
lean_dec_ref(v_pivot_2402_);
v___x_2407_ = lean_array_fswap(v_as_2403_, v_i_2404_, v_hi_2401_);
v___x_2408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2408_, 0, v_i_2404_);
lean_ctor_set(v___x_2408_, 1, v___x_2407_);
return v___x_2408_;
}
else
{
lean_object* v___x_2409_; lean_object* v_fst_2410_; lean_object* v_fst_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; uint8_t v___x_2414_; 
v___x_2409_ = lean_array_fget_borrowed(v_as_2403_, v_k_2405_);
v_fst_2410_ = lean_ctor_get(v___x_2409_, 0);
v_fst_2411_ = lean_ctor_get(v_pivot_2402_, 0);
lean_inc(v_fst_2410_);
v___x_2412_ = l_Lean_Name_toString(v_fst_2410_, v___x_2406_);
lean_inc(v_fst_2411_);
v___x_2413_ = l_Lean_Name_toString(v_fst_2411_, v___x_2406_);
v___x_2414_ = lean_string_dec_lt(v___x_2412_, v___x_2413_);
lean_dec_ref(v___x_2413_);
lean_dec_ref(v___x_2412_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2415_ = lean_unsigned_to_nat(1u);
v___x_2416_ = lean_nat_add(v_k_2405_, v___x_2415_);
lean_dec(v_k_2405_);
v_k_2405_ = v___x_2416_;
goto _start;
}
else
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2418_ = lean_array_fswap(v_as_2403_, v_i_2404_, v_k_2405_);
v___x_2419_ = lean_unsigned_to_nat(1u);
v___x_2420_ = lean_nat_add(v_i_2404_, v___x_2419_);
lean_dec(v_i_2404_);
v___x_2421_ = lean_nat_add(v_k_2405_, v___x_2419_);
lean_dec(v_k_2405_);
v_as_2403_ = v___x_2418_;
v_i_2404_ = v___x_2420_;
v_k_2405_ = v___x_2421_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg___boxed(lean_object* v_hi_2423_, lean_object* v_pivot_2424_, lean_object* v_as_2425_, lean_object* v_i_2426_, lean_object* v_k_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_2423_, v_pivot_2424_, v_as_2425_, v_i_2426_, v_k_2427_);
lean_dec(v_hi_2423_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(lean_object* v_n_2429_, lean_object* v_as_2430_, lean_object* v_lo_2431_, lean_object* v_hi_2432_){
_start:
{
lean_object* v___y_2434_; uint8_t v___x_2444_; 
v___x_2444_ = lean_nat_dec_lt(v_lo_2431_, v_hi_2432_);
if (v___x_2444_ == 0)
{
lean_dec(v_lo_2431_);
return v_as_2430_;
}
else
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v_mid_2447_; lean_object* v___y_2449_; lean_object* v___y_2455_; lean_object* v___x_2460_; lean_object* v___x_2461_; uint8_t v___x_2462_; 
v___x_2445_ = lean_nat_add(v_lo_2431_, v_hi_2432_);
v___x_2446_ = lean_unsigned_to_nat(1u);
v_mid_2447_ = lean_nat_shiftr(v___x_2445_, v___x_2446_);
lean_dec(v___x_2445_);
v___x_2460_ = lean_array_fget_borrowed(v_as_2430_, v_mid_2447_);
v___x_2461_ = lean_array_fget_borrowed(v_as_2430_, v_lo_2431_);
lean_inc(v___x_2461_);
lean_inc(v___x_2460_);
v___x_2462_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2444_, v___x_2460_, v___x_2461_);
if (v___x_2462_ == 0)
{
v___y_2455_ = v_as_2430_;
goto v___jp_2454_;
}
else
{
lean_object* v___x_2463_; 
v___x_2463_ = lean_array_fswap(v_as_2430_, v_lo_2431_, v_mid_2447_);
v___y_2455_ = v___x_2463_;
goto v___jp_2454_;
}
v___jp_2448_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; uint8_t v___x_2452_; 
v___x_2450_ = lean_array_fget_borrowed(v___y_2449_, v_mid_2447_);
v___x_2451_ = lean_array_fget_borrowed(v___y_2449_, v_hi_2432_);
lean_inc(v___x_2451_);
lean_inc(v___x_2450_);
v___x_2452_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2444_, v___x_2450_, v___x_2451_);
if (v___x_2452_ == 0)
{
lean_dec(v_mid_2447_);
v___y_2434_ = v___y_2449_;
goto v___jp_2433_;
}
else
{
lean_object* v___x_2453_; 
v___x_2453_ = lean_array_fswap(v___y_2449_, v_mid_2447_, v_hi_2432_);
lean_dec(v_mid_2447_);
v___y_2434_ = v___x_2453_;
goto v___jp_2433_;
}
}
v___jp_2454_:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; 
v___x_2456_ = lean_array_fget_borrowed(v___y_2455_, v_hi_2432_);
v___x_2457_ = lean_array_fget_borrowed(v___y_2455_, v_lo_2431_);
lean_inc(v___x_2457_);
lean_inc(v___x_2456_);
v___x_2458_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2444_, v___x_2456_, v___x_2457_);
if (v___x_2458_ == 0)
{
v___y_2449_ = v___y_2455_;
goto v___jp_2448_;
}
else
{
lean_object* v___x_2459_; 
v___x_2459_ = lean_array_fswap(v___y_2455_, v_lo_2431_, v_hi_2432_);
v___y_2449_ = v___x_2459_;
goto v___jp_2448_;
}
}
}
v___jp_2433_:
{
lean_object* v_pivot_2435_; lean_object* v___x_2436_; lean_object* v_fst_2437_; lean_object* v_snd_2438_; uint8_t v___x_2439_; 
v_pivot_2435_ = lean_array_fget(v___y_2434_, v_hi_2432_);
lean_inc_n(v_lo_2431_, 2);
v___x_2436_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_2432_, v_pivot_2435_, v___y_2434_, v_lo_2431_, v_lo_2431_);
v_fst_2437_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_fst_2437_);
v_snd_2438_ = lean_ctor_get(v___x_2436_, 1);
lean_inc(v_snd_2438_);
lean_dec_ref(v___x_2436_);
v___x_2439_ = lean_nat_dec_le(v_hi_2432_, v_fst_2437_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2440_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_2429_, v_snd_2438_, v_lo_2431_, v_fst_2437_);
v___x_2441_ = lean_unsigned_to_nat(1u);
v___x_2442_ = lean_nat_add(v_fst_2437_, v___x_2441_);
lean_dec(v_fst_2437_);
v_as_2430_ = v___x_2440_;
v_lo_2431_ = v___x_2442_;
goto _start;
}
else
{
lean_dec(v_fst_2437_);
lean_dec(v_lo_2431_);
return v_snd_2438_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___boxed(lean_object* v_n_2464_, lean_object* v_as_2465_, lean_object* v_lo_2466_, lean_object* v_hi_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_2464_, v_as_2465_, v_lo_2466_, v_hi_2467_);
lean_dec(v_hi_2467_);
lean_dec(v_n_2464_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(lean_object* v_init_2469_, lean_object* v_x_2470_){
_start:
{
if (lean_obj_tag(v_x_2470_) == 0)
{
lean_object* v_k_2471_; lean_object* v_v_2472_; lean_object* v_l_2473_; lean_object* v_r_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v_k_2471_ = lean_ctor_get(v_x_2470_, 1);
v_v_2472_ = lean_ctor_get(v_x_2470_, 2);
v_l_2473_ = lean_ctor_get(v_x_2470_, 3);
v_r_2474_ = lean_ctor_get(v_x_2470_, 4);
v___x_2475_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_2469_, v_l_2473_);
lean_inc(v_v_2472_);
lean_inc(v_k_2471_);
v___x_2476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2476_, 0, v_k_2471_);
lean_ctor_set(v___x_2476_, 1, v_v_2472_);
v___x_2477_ = lean_array_push(v___x_2475_, v___x_2476_);
v_init_2469_ = v___x_2477_;
v_x_2470_ = v_r_2474_;
goto _start;
}
else
{
return v_init_2469_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25___boxed(lean_object* v_init_2479_, lean_object* v_x_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_2479_, v_x_2480_);
lean_dec(v_x_2480_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(lean_object* v_as_2482_, size_t v_sz_2483_, size_t v_i_2484_, lean_object* v_b_2485_){
_start:
{
uint8_t v___x_2487_; 
v___x_2487_ = lean_usize_dec_lt(v_i_2484_, v_sz_2483_);
if (v___x_2487_ == 0)
{
lean_object* v___x_2488_; 
v___x_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2488_, 0, v_b_2485_);
return v___x_2488_;
}
else
{
lean_object* v_a_2489_; lean_object* v_fst_2490_; lean_object* v_snd_2491_; lean_object* v_found_2492_; size_t v___x_2493_; size_t v___x_2494_; 
v_a_2489_ = lean_array_uget_borrowed(v_as_2482_, v_i_2484_);
v_fst_2490_ = lean_ctor_get(v_a_2489_, 0);
v_snd_2491_ = lean_ctor_get(v_a_2489_, 1);
lean_inc(v_snd_2491_);
lean_inc(v_fst_2490_);
v_found_2492_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2490_, v_snd_2491_, v_b_2485_);
v___x_2493_ = ((size_t)1ULL);
v___x_2494_ = lean_usize_add(v_i_2484_, v___x_2493_);
v_i_2484_ = v___x_2494_;
v_b_2485_ = v_found_2492_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg___boxed(lean_object* v_as_2496_, lean_object* v_sz_2497_, lean_object* v_i_2498_, lean_object* v_b_2499_, lean_object* v___y_2500_){
_start:
{
size_t v_sz_boxed_2501_; size_t v_i_boxed_2502_; lean_object* v_res_2503_; 
v_sz_boxed_2501_ = lean_unbox_usize(v_sz_2497_);
lean_dec(v_sz_2497_);
v_i_boxed_2502_ = lean_unbox_usize(v_i_2498_);
lean_dec(v_i_2498_);
v_res_2503_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_2496_, v_sz_boxed_2501_, v_i_boxed_2502_, v_b_2499_);
lean_dec_ref(v_as_2496_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object* v_as_2504_, size_t v_sz_2505_, size_t v_i_2506_, lean_object* v_b_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
uint8_t v___x_2511_; 
v___x_2511_ = lean_usize_dec_lt(v_i_2506_, v_sz_2505_);
if (v___x_2511_ == 0)
{
lean_object* v___x_2512_; 
v___x_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2512_, 0, v_b_2507_);
return v___x_2512_;
}
else
{
lean_object* v_a_2513_; size_t v_sz_2514_; size_t v___x_2515_; lean_object* v___x_2516_; 
v_a_2513_ = lean_array_uget_borrowed(v_as_2504_, v_i_2506_);
v_sz_2514_ = lean_array_size(v_a_2513_);
v___x_2515_ = ((size_t)0ULL);
v___x_2516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_a_2513_, v_sz_2514_, v___x_2515_, v_b_2507_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; size_t v___x_2518_; size_t v___x_2519_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v___x_2516_, 1);
v___x_2518_ = ((size_t)1ULL);
v___x_2519_ = lean_usize_add(v_i_2506_, v___x_2518_);
v_i_2506_ = v___x_2519_;
v_b_2507_ = v_a_2517_;
goto _start;
}
else
{
return v___x_2516_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object* v_as_2521_, lean_object* v_sz_2522_, lean_object* v_i_2523_, lean_object* v_b_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
size_t v_sz_boxed_2528_; size_t v_i_boxed_2529_; lean_object* v_res_2530_; 
v_sz_boxed_2528_ = lean_unbox_usize(v_sz_2522_);
lean_dec(v_sz_2522_);
v_i_boxed_2529_ = lean_unbox_usize(v_i_2523_);
lean_dec(v_i_2523_);
v_res_2530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_as_2521_, v_sz_boxed_2528_, v_i_boxed_2529_, v_b_2524_, v___y_2525_, v___y_2526_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec_ref(v_as_2521_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v___y_2537_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v_env_2555_; lean_object* v___x_2556_; lean_object* v_toEnvExtension_2557_; lean_object* v_asyncMode_2558_; lean_object* v___x_2559_; lean_object* v_a_2561_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v_a_2586_; lean_object* v_a_2587_; 
v___x_2552_ = lean_box(1);
v___x_2553_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_2554_ = lean_st_ref_get(v___y_2534_);
v_env_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc_ref_n(v_env_2555_, 2);
lean_dec(v___x_2554_);
v___x_2556_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2557_ = lean_ctor_get(v___x_2556_, 0);
v_asyncMode_2558_ = lean_ctor_get(v_toEnvExtension_2557_, 2);
v___x_2559_ = lean_box(0);
v___x_2584_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2552_, v___x_2556_, v_env_2555_, v_asyncMode_2558_, v___x_2559_);
v___x_2585_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v___x_2552_, v___x_2584_);
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_a_2586_);
lean_dec_ref(v___x_2585_);
v_a_2587_ = lean_ctor_get(v_a_2586_, 0);
lean_inc(v_a_2587_);
lean_dec(v_a_2586_);
v_a_2561_ = v_a_2587_;
goto v___jp_2560_;
v___jp_2536_:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = lean_array_to_list(v___y_2537_);
v___x_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2538_);
return v___x_2539_;
}
v___jp_2540_:
{
lean_object* v___x_2545_; 
v___x_2545_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v___y_2542_, v___y_2543_, v___y_2541_, v___y_2544_);
lean_dec(v___y_2544_);
lean_dec(v___y_2542_);
v___y_2537_ = v___x_2545_;
goto v___jp_2536_;
}
v___jp_2546_:
{
uint8_t v___x_2551_; 
v___x_2551_ = lean_nat_dec_le(v___y_2550_, v___y_2547_);
if (v___x_2551_ == 0)
{
lean_dec(v___y_2547_);
lean_inc(v___y_2550_);
v___y_2541_ = v___y_2550_;
v___y_2542_ = v___y_2548_;
v___y_2543_ = v___y_2549_;
v___y_2544_ = v___y_2550_;
goto v___jp_2540_;
}
else
{
v___y_2541_ = v___y_2550_;
v___y_2542_ = v___y_2548_;
v___y_2543_ = v___y_2549_;
v___y_2544_ = v___y_2547_;
goto v___jp_2540_;
}
}
v___jp_2560_:
{
lean_object* v___x_2562_; lean_object* v_importedEntries_2563_; size_t v_sz_2564_; size_t v___x_2565_; lean_object* v___x_2566_; 
v___x_2562_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2553_, v_toEnvExtension_2557_, v_env_2555_, v_asyncMode_2558_, v___x_2559_);
v_importedEntries_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc_ref(v_importedEntries_2563_);
lean_dec(v___x_2562_);
v_sz_2564_ = lean_array_size(v_importedEntries_2563_);
v___x_2565_ = ((size_t)0ULL);
v___x_2566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_importedEntries_2563_, v_sz_2564_, v___x_2565_, v_a_2561_, v___y_2533_, v___y_2534_);
lean_dec_ref(v_importedEntries_2563_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v_arr_2570_; lean_object* v___x_2571_; uint8_t v___x_2572_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2567_);
lean_dec_ref_known(v___x_2566_, 1);
v___x_2568_ = lean_unsigned_to_nat(0u);
v___x_2569_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0));
v_arr_2570_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v___x_2569_, v_a_2567_);
lean_dec(v_a_2567_);
v___x_2571_ = lean_array_get_size(v_arr_2570_);
v___x_2572_ = lean_nat_dec_eq(v___x_2571_, v___x_2568_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; lean_object* v___x_2574_; uint8_t v___x_2575_; 
v___x_2573_ = lean_unsigned_to_nat(1u);
v___x_2574_ = lean_nat_sub(v___x_2571_, v___x_2573_);
v___x_2575_ = lean_nat_dec_le(v___x_2568_, v___x_2574_);
if (v___x_2575_ == 0)
{
lean_inc(v___x_2574_);
v___y_2547_ = v___x_2574_;
v___y_2548_ = v___x_2571_;
v___y_2549_ = v_arr_2570_;
v___y_2550_ = v___x_2574_;
goto v___jp_2546_;
}
else
{
v___y_2547_ = v___x_2574_;
v___y_2548_ = v___x_2571_;
v___y_2549_ = v_arr_2570_;
v___y_2550_ = v___x_2568_;
goto v___jp_2546_;
}
}
else
{
v___y_2537_ = v_arr_2570_;
goto v___jp_2536_;
}
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
v_a_2576_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v___x_2566_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2566_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v___y_2588_, v___y_2589_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object* v_t_2592_, lean_object* v_k_2593_, lean_object* v_fallback_2594_){
_start:
{
if (lean_obj_tag(v_t_2592_) == 0)
{
lean_object* v_k_2595_; lean_object* v_v_2596_; lean_object* v_l_2597_; lean_object* v_r_2598_; uint8_t v___x_2599_; 
v_k_2595_ = lean_ctor_get(v_t_2592_, 1);
v_v_2596_ = lean_ctor_get(v_t_2592_, 2);
v_l_2597_ = lean_ctor_get(v_t_2592_, 3);
v_r_2598_ = lean_ctor_get(v_t_2592_, 4);
v___x_2599_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2593_, v_k_2595_);
switch(v___x_2599_)
{
case 0:
{
v_t_2592_ = v_l_2597_;
goto _start;
}
case 1:
{
lean_inc(v_v_2596_);
return v_v_2596_;
}
default: 
{
v_t_2592_ = v_r_2598_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2594_);
return v_fallback_2594_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object* v_t_2602_, lean_object* v_k_2603_, lean_object* v_fallback_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_2602_, v_k_2603_, v_fallback_2604_);
lean_dec(v_fallback_2604_);
lean_dec(v_k_2603_);
lean_dec(v_t_2602_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object* v_as_2606_, size_t v_sz_2607_, size_t v_i_2608_, lean_object* v_b_2609_){
_start:
{
uint8_t v___x_2611_; 
v___x_2611_ = lean_usize_dec_lt(v_i_2608_, v_sz_2607_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; 
v___x_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2612_, 0, v_b_2609_);
return v___x_2612_;
}
else
{
lean_object* v_a_2613_; lean_object* v_fst_2614_; lean_object* v_snd_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; size_t v___x_2620_; size_t v___x_2621_; 
v_a_2613_ = lean_array_uget_borrowed(v_as_2606_, v_i_2608_);
v_fst_2614_ = lean_ctor_get(v_a_2613_, 0);
v_snd_2615_ = lean_ctor_get(v_a_2613_, 1);
v___x_2616_ = l_Lean_NameSet_empty;
v___x_2617_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_2609_, v_snd_2615_, v___x_2616_);
lean_inc(v_fst_2614_);
v___x_2618_ = l_Lean_NameSet_insert(v___x_2617_, v_fst_2614_);
lean_inc(v_snd_2615_);
v___x_2619_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_snd_2615_, v___x_2618_, v_b_2609_);
v___x_2620_ = ((size_t)1ULL);
v___x_2621_ = lean_usize_add(v_i_2608_, v___x_2620_);
v_i_2608_ = v___x_2621_;
v_b_2609_ = v___x_2619_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object* v_as_2623_, lean_object* v_sz_2624_, lean_object* v_i_2625_, lean_object* v_b_2626_, lean_object* v___y_2627_){
_start:
{
size_t v_sz_boxed_2628_; size_t v_i_boxed_2629_; lean_object* v_res_2630_; 
v_sz_boxed_2628_ = lean_unbox_usize(v_sz_2624_);
lean_dec(v_sz_2624_);
v_i_boxed_2629_ = lean_unbox_usize(v_i_2625_);
lean_dec(v_i_2625_);
v_res_2630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_2623_, v_sz_boxed_2628_, v_i_boxed_2629_, v_b_2626_);
lean_dec_ref(v_as_2623_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object* v_as_2631_, size_t v_sz_2632_, size_t v_i_2633_, lean_object* v_b_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
uint8_t v___x_2638_; 
v___x_2638_ = lean_usize_dec_lt(v_i_2633_, v_sz_2632_);
if (v___x_2638_ == 0)
{
lean_object* v___x_2639_; 
v___x_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2639_, 0, v_b_2634_);
return v___x_2639_;
}
else
{
lean_object* v_a_2640_; size_t v_sz_2641_; size_t v___x_2642_; lean_object* v___x_2643_; 
v_a_2640_ = lean_array_uget_borrowed(v_as_2631_, v_i_2633_);
v_sz_2641_ = lean_array_size(v_a_2640_);
v___x_2642_ = ((size_t)0ULL);
v___x_2643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_a_2640_, v_sz_2641_, v___x_2642_, v_b_2634_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; size_t v___x_2645_; size_t v___x_2646_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v___x_2643_, 1);
v___x_2645_ = ((size_t)1ULL);
v___x_2646_ = lean_usize_add(v_i_2633_, v___x_2645_);
v_i_2633_ = v___x_2646_;
v_b_2634_ = v_a_2644_;
goto _start;
}
else
{
return v___x_2643_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object* v_as_2648_, lean_object* v_sz_2649_, lean_object* v_i_2650_, lean_object* v_b_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
size_t v_sz_boxed_2655_; size_t v_i_boxed_2656_; lean_object* v_res_2657_; 
v_sz_boxed_2655_ = lean_unbox_usize(v_sz_2649_);
lean_dec(v_sz_2649_);
v_i_boxed_2656_ = lean_unbox_usize(v_i_2650_);
lean_dec(v_i_2650_);
v_res_2657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v_as_2648_, v_sz_boxed_2655_, v_i_boxed_2656_, v_b_2651_, v___y_2652_, v___y_2653_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec_ref(v_as_2648_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object* v_as_2658_, size_t v_i_2659_, size_t v_stop_2660_, lean_object* v_b_2661_){
_start:
{
uint8_t v___x_2662_; 
v___x_2662_ = lean_usize_dec_eq(v_i_2659_, v_stop_2660_);
if (v___x_2662_ == 0)
{
lean_object* v___x_2663_; lean_object* v_fst_2664_; lean_object* v_snd_2665_; lean_object* v___x_2666_; size_t v___x_2667_; size_t v___x_2668_; 
v___x_2663_ = lean_array_uget_borrowed(v_as_2658_, v_i_2659_);
v_fst_2664_ = lean_ctor_get(v___x_2663_, 0);
v_snd_2665_ = lean_ctor_get(v___x_2663_, 1);
lean_inc(v_snd_2665_);
lean_inc(v_fst_2664_);
v___x_2666_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2664_, v_snd_2665_, v_b_2661_);
v___x_2667_ = ((size_t)1ULL);
v___x_2668_ = lean_usize_add(v_i_2659_, v___x_2667_);
v_i_2659_ = v___x_2668_;
v_b_2661_ = v___x_2666_;
goto _start;
}
else
{
return v_b_2661_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object* v_as_2670_, lean_object* v_i_2671_, lean_object* v_stop_2672_, lean_object* v_b_2673_){
_start:
{
size_t v_i_boxed_2674_; size_t v_stop_boxed_2675_; lean_object* v_res_2676_; 
v_i_boxed_2674_ = lean_unbox_usize(v_i_2671_);
lean_dec(v_i_2671_);
v_stop_boxed_2675_ = lean_unbox_usize(v_stop_2672_);
lean_dec(v_stop_2672_);
v_res_2676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v_as_2670_, v_i_boxed_2674_, v_stop_boxed_2675_, v_b_2673_);
lean_dec_ref(v_as_2670_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object* v_as_2677_, size_t v_i_2678_, size_t v_stop_2679_, lean_object* v_b_2680_){
_start:
{
lean_object* v___y_2682_; uint8_t v___x_2686_; 
v___x_2686_ = lean_usize_dec_eq(v_i_2678_, v_stop_2679_);
if (v___x_2686_ == 0)
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; uint8_t v___x_2690_; 
v___x_2687_ = lean_array_uget_borrowed(v_as_2677_, v_i_2678_);
v___x_2688_ = lean_unsigned_to_nat(0u);
v___x_2689_ = lean_array_get_size(v___x_2687_);
v___x_2690_ = lean_nat_dec_lt(v___x_2688_, v___x_2689_);
if (v___x_2690_ == 0)
{
v___y_2682_ = v_b_2680_;
goto v___jp_2681_;
}
else
{
size_t v___x_2691_; size_t v___x_2692_; lean_object* v___x_2693_; 
v___x_2691_ = ((size_t)0ULL);
v___x_2692_ = lean_usize_of_nat(v___x_2689_);
v___x_2693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_2687_, v___x_2691_, v___x_2692_, v_b_2680_);
v___y_2682_ = v___x_2693_;
goto v___jp_2681_;
}
}
else
{
return v_b_2680_;
}
v___jp_2681_:
{
size_t v___x_2683_; size_t v___x_2684_; 
v___x_2683_ = ((size_t)1ULL);
v___x_2684_ = lean_usize_add(v_i_2678_, v___x_2683_);
v_i_2678_ = v___x_2684_;
v_b_2680_ = v___y_2682_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object* v_as_2694_, lean_object* v_i_2695_, lean_object* v_stop_2696_, lean_object* v_b_2697_){
_start:
{
size_t v_i_boxed_2698_; size_t v_stop_boxed_2699_; lean_object* v_res_2700_; 
v_i_boxed_2698_ = lean_unbox_usize(v_i_2695_);
lean_dec(v_i_2695_);
v_stop_boxed_2699_ = lean_unbox_usize(v_stop_2696_);
lean_dec(v_stop_2696_);
v_res_2700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v_as_2694_, v_i_boxed_2698_, v_stop_boxed_2699_, v_b_2697_);
lean_dec_ref(v_as_2694_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object* v___y_2701_){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v_env_2707_; lean_object* v___x_2708_; lean_object* v_ext_2709_; lean_object* v_toEnvExtension_2710_; lean_object* v_asyncMode_2711_; lean_object* v___x_2712_; lean_object* v_categories_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2703_ = lean_box(1);
v___x_2704_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_2705_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2706_ = lean_st_ref_get(v___y_2701_);
v_env_2707_ = lean_ctor_get(v___x_2706_, 0);
lean_inc_ref_n(v_env_2707_, 2);
lean_dec(v___x_2706_);
v___x_2708_ = l_Lean_Parser_parserExtension;
v_ext_2709_ = lean_ctor_get(v___x_2708_, 1);
v_toEnvExtension_2710_ = lean_ctor_get(v_ext_2709_, 0);
v_asyncMode_2711_ = lean_ctor_get(v_toEnvExtension_2710_, 2);
v___x_2712_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2705_, v___x_2708_, v_env_2707_, v_asyncMode_2711_);
v_categories_2713_ = lean_ctor_get(v___x_2712_, 2);
lean_inc_ref(v_categories_2713_);
lean_dec(v___x_2712_);
v___x_2714_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_2715_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_2713_, v___x_2714_);
lean_dec_ref(v_categories_2713_);
if (lean_obj_tag(v___x_2715_) == 1)
{
lean_object* v_val_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2747_; 
v_val_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2747_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_val_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2747_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___y_2721_; lean_object* v___x_2730_; lean_object* v_toEnvExtension_2731_; lean_object* v_exportEntriesFn_2732_; lean_object* v_asyncMode_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v_importedEntries_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v_exported_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; 
v___x_2730_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_2731_ = lean_ctor_get(v___x_2730_, 0);
v_exportEntriesFn_2732_ = lean_ctor_get(v___x_2730_, 4);
v_asyncMode_2733_ = lean_ctor_get(v_toEnvExtension_2731_, 2);
v___x_2734_ = lean_box(0);
lean_inc_ref_n(v_env_2707_, 2);
v___x_2735_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2704_, v_toEnvExtension_2731_, v_env_2707_, v_asyncMode_2733_, v___x_2734_);
v_importedEntries_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc_ref(v_importedEntries_2736_);
lean_dec(v___x_2735_);
v___x_2737_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2703_, v___x_2730_, v_env_2707_, v_asyncMode_2733_, v___x_2734_);
lean_inc_ref(v_exportEntriesFn_2732_);
v___x_2738_ = lean_apply_2(v_exportEntriesFn_2732_, v_env_2707_, v___x_2737_);
v_exported_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_exported_2739_);
lean_dec_ref(v___x_2738_);
v___x_2740_ = lean_array_push(v_importedEntries_2736_, v_exported_2739_);
v___x_2741_ = lean_unsigned_to_nat(0u);
v___x_2742_ = lean_array_get_size(v___x_2740_);
v___x_2743_ = lean_nat_dec_lt(v___x_2741_, v___x_2742_);
if (v___x_2743_ == 0)
{
lean_dec_ref(v___x_2740_);
v___y_2721_ = v___x_2703_;
goto v___jp_2720_;
}
else
{
size_t v___x_2744_; size_t v___x_2745_; lean_object* v___x_2746_; 
v___x_2744_ = ((size_t)0ULL);
v___x_2745_ = lean_usize_of_nat(v___x_2742_);
v___x_2746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_2740_, v___x_2744_, v___x_2745_, v___x_2703_);
lean_dec_ref(v___x_2740_);
v___y_2721_ = v___x_2746_;
goto v___jp_2720_;
}
v___jp_2720_:
{
lean_object* v_tables_2722_; lean_object* v_leadingTable_2723_; lean_object* v_trailingTable_2724_; lean_object* v_firstTokens_2725_; lean_object* v_firstTokens_2726_; lean_object* v___x_2728_; 
v_tables_2722_ = lean_ctor_get(v_val_2716_, 2);
v_leadingTable_2723_ = lean_ctor_get(v_tables_2722_, 0);
v_trailingTable_2724_ = lean_ctor_get(v_tables_2722_, 2);
lean_inc(v_trailingTable_2724_);
lean_inc(v_leadingTable_2723_);
lean_inc(v_val_2716_);
v_firstTokens_2725_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2716_, v_leadingTable_2723_, v___y_2721_);
v_firstTokens_2726_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2716_, v_trailingTable_2724_, v_firstTokens_2725_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set_tag(v___x_2718_, 0);
lean_ctor_set(v___x_2718_, 0, v_firstTokens_2726_);
v___x_2728_ = v___x_2718_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_firstTokens_2726_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
else
{
lean_object* v___x_2748_; 
lean_dec(v___x_2715_);
lean_dec_ref(v_env_2707_);
v___x_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2703_);
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
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0));
v___x_2754_ = l_Lean_stringToMessageData(v___x_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object* v_a_2755_, lean_object* v_a_2756_){
_start:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v_env_2761_; lean_object* v___x_2762_; lean_object* v_env_2763_; lean_object* v___x_2764_; lean_object* v_env_2765_; lean_object* v___x_2766_; lean_object* v_toEnvExtension_2767_; lean_object* v_exportEntriesFn_2768_; lean_object* v_asyncMode_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v_importedEntries_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2824_; 
v___x_2758_ = lean_box(1);
v___x_2759_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_2760_ = lean_st_ref_get(v_a_2756_);
v_env_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc_ref(v_env_2761_);
lean_dec(v___x_2760_);
v___x_2762_ = lean_st_ref_get(v_a_2756_);
v_env_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc_ref(v_env_2763_);
lean_dec(v___x_2762_);
v___x_2764_ = lean_st_ref_get(v_a_2756_);
v_env_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc_ref(v_env_2765_);
lean_dec(v___x_2764_);
v___x_2766_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_2767_ = lean_ctor_get(v___x_2766_, 0);
v_exportEntriesFn_2768_ = lean_ctor_get(v___x_2766_, 4);
v_asyncMode_2769_ = lean_ctor_get(v_toEnvExtension_2767_, 2);
v___x_2770_ = lean_box(0);
v___x_2771_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2759_, v_toEnvExtension_2767_, v_env_2761_, v_asyncMode_2769_, v___x_2770_);
v_importedEntries_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2824_ == 0)
{
lean_object* v_unused_2825_; 
v_unused_2825_ = lean_ctor_get(v___x_2771_, 1);
lean_dec(v_unused_2825_);
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2824_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_importedEntries_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2824_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v_exported_2778_; lean_object* v___x_2779_; size_t v_sz_2780_; size_t v___x_2781_; lean_object* v___x_2782_; 
v___x_2776_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2758_, v___x_2766_, v_env_2765_, v_asyncMode_2769_, v___x_2770_);
lean_inc_ref(v_exportEntriesFn_2768_);
v___x_2777_ = lean_apply_2(v_exportEntriesFn_2768_, v_env_2763_, v___x_2776_);
v_exported_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_exported_2778_);
lean_dec_ref(v___x_2777_);
v___x_2779_ = lean_array_push(v_importedEntries_2772_, v_exported_2778_);
v_sz_2780_ = lean_array_size(v___x_2779_);
v___x_2781_ = ((size_t)0ULL);
v___x_2782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v___x_2779_, v_sz_2780_, v___x_2781_, v___x_2758_, v_a_2755_, v_a_2756_);
lean_dec_ref(v___x_2779_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2784_; lean_object* v_a_2785_; lean_object* v___x_2786_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2783_);
lean_dec_ref_known(v___x_2782_, 1);
v___x_2784_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v_a_2756_);
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2785_);
lean_dec_ref(v___x_2784_);
v___x_2786_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v_a_2755_, v_a_2756_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref_known(v___x_2786_, 1);
v___x_2788_ = lean_box(0);
v___x_2789_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_2785_, v_a_2783_, v_a_2787_, v___x_2788_, v_a_2755_, v_a_2756_);
lean_dec(v_a_2783_);
lean_dec(v_a_2785_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2795_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2789_, 1);
v___x_2791_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1);
v___x_2792_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2793_ = l_Lean_MessageData_joinSep(v_a_2790_, v___x_2792_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set_tag(v___x_2774_, 7);
lean_ctor_set(v___x_2774_, 1, v___x_2793_);
lean_ctor_set(v___x_2774_, 0, v___x_2792_);
v___x_2795_ = v___x_2774_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2792_);
lean_ctor_set(v_reuseFailAlloc_2799_, 1, v___x_2793_);
v___x_2795_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2796_ = l_Lean_MessageData_nestD(v___x_2795_);
v___x_2797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2791_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
v___x_2798_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v___x_2797_, v_a_2755_, v_a_2756_);
return v___x_2798_;
}
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_del_object(v___x_2774_);
v_a_2800_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2789_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2789_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
lean_dec(v_a_2785_);
lean_dec(v_a_2783_);
lean_del_object(v___x_2774_);
v_a_2808_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2786_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2786_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_del_object(v___x_2774_);
v_a_2816_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2782_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2782_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_2826_, v_a_2827_);
lean_dec(v_a_2827_);
lean_dec_ref(v_a_2826_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object* v___stx_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_){
_start:
{
lean_object* v___x_2834_; 
v___x_2834_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_2831_, v_a_2832_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object* v___stx_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags(v___stx_2835_, v_a_2836_, v_a_2837_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
lean_dec(v___stx_2835_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object* v_00_u03b4_2840_, lean_object* v_t_2841_, lean_object* v_k_2842_, lean_object* v_fallback_2843_){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_2841_, v_k_2842_, v_fallback_2843_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object* v_00_u03b4_2845_, lean_object* v_t_2846_, lean_object* v_k_2847_, lean_object* v_fallback_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(v_00_u03b4_2845_, v_t_2846_, v_k_2847_, v_fallback_2848_);
lean_dec(v_fallback_2848_);
lean_dec(v_k_2847_);
lean_dec(v_t_2846_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object* v_as_2850_, size_t v_sz_2851_, size_t v_i_2852_, lean_object* v_b_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v___x_2857_; 
v___x_2857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_2850_, v_sz_2851_, v_i_2852_, v_b_2853_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object* v_as_2858_, lean_object* v_sz_2859_, lean_object* v_i_2860_, lean_object* v_b_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
size_t v_sz_boxed_2865_; size_t v_i_boxed_2866_; lean_object* v_res_2867_; 
v_sz_boxed_2865_ = lean_unbox_usize(v_sz_2859_);
lean_dec(v_sz_2859_);
v_i_boxed_2866_ = lean_unbox_usize(v_i_2860_);
lean_dec(v_i_2860_);
v_res_2867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(v_as_2858_, v_sz_boxed_2865_, v_i_boxed_2866_, v_b_2861_, v___y_2862_, v___y_2863_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec_ref(v_as_2858_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v___x_2871_; 
v___x_2871_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_2869_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(v___y_2872_, v___y_2873_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object* v_val_2876_, lean_object* v___x_2877_, lean_object* v___x_2878_, lean_object* v_inst_2879_, lean_object* v_R_2880_, lean_object* v_a_2881_, lean_object* v_b_2882_){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2876_, v___x_2877_, v___x_2878_, v_a_2881_, v_b_2882_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object* v_val_2884_, lean_object* v___x_2885_, lean_object* v___x_2886_, lean_object* v_inst_2887_, lean_object* v_R_2888_, lean_object* v_a_2889_, lean_object* v_b_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(v_val_2884_, v___x_2885_, v___x_2886_, v_inst_2887_, v_R_2888_, v_a_2889_, v_b_2890_);
lean_dec_ref(v___x_2885_);
lean_dec_ref(v_val_2884_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object* v_init_2892_, lean_object* v_t_2893_){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_2892_, v_t_2893_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object* v_n_2895_, lean_object* v_as_2896_, lean_object* v_lo_2897_, lean_object* v_hi_2898_, lean_object* v_w_2899_, lean_object* v_hlo_2900_, lean_object* v_hhi_2901_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_2895_, v_as_2896_, v_lo_2897_, v_hi_2898_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object* v_n_2903_, lean_object* v_as_2904_, lean_object* v_lo_2905_, lean_object* v_hi_2906_, lean_object* v_w_2907_, lean_object* v_hlo_2908_, lean_object* v_hhi_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(v_n_2903_, v_as_2904_, v_lo_2905_, v_hi_2906_, v_w_2907_, v_hlo_2908_, v_hhi_2909_);
lean_dec(v_hi_2906_);
lean_dec(v_n_2903_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object* v_00_u03b2_2911_, lean_object* v_x_2912_, lean_object* v_x_2913_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_2912_, v_x_2913_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2915_, lean_object* v_x_2916_, lean_object* v_x_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(v_00_u03b2_2915_, v_x_2916_, v_x_2917_);
lean_dec(v_x_2917_);
lean_dec_ref(v_x_2916_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object* v_tac_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_2919_, v___y_2921_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object* v_tac_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(v_tac_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object* v_00_u03b4_2929_, lean_object* v_t_2930_, lean_object* v_k_2931_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_2930_, v_k_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___boxed(lean_object* v_00_u03b4_2933_, lean_object* v_t_2934_, lean_object* v_k_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(v_00_u03b4_2933_, v_t_2934_, v_k_2935_);
lean_dec(v_k_2935_);
lean_dec(v_t_2934_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object* v_00_u03b2_2937_, lean_object* v_x_2938_, lean_object* v_x_2939_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_2938_, v_x_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object* v_00_u03b2_2941_, lean_object* v_x_2942_, lean_object* v_x_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(v_00_u03b2_2941_, v_x_2942_, v_x_2943_);
lean_dec(v_x_2943_);
lean_dec_ref(v_x_2942_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(lean_object* v_n_2945_, lean_object* v_lo_2946_, lean_object* v_hi_2947_, lean_object* v_hhi_2948_, lean_object* v_pivot_2949_, lean_object* v_as_2950_, lean_object* v_i_2951_, lean_object* v_k_2952_, lean_object* v_ilo_2953_, lean_object* v_ik_2954_, lean_object* v_w_2955_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_2947_, v_pivot_2949_, v_as_2950_, v_i_2951_, v_k_2952_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___boxed(lean_object* v_n_2957_, lean_object* v_lo_2958_, lean_object* v_hi_2959_, lean_object* v_hhi_2960_, lean_object* v_pivot_2961_, lean_object* v_as_2962_, lean_object* v_i_2963_, lean_object* v_k_2964_, lean_object* v_ilo_2965_, lean_object* v_ik_2966_, lean_object* v_w_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(v_n_2957_, v_lo_2958_, v_hi_2959_, v_hhi_2960_, v_pivot_2961_, v_as_2962_, v_i_2963_, v_k_2964_, v_ilo_2965_, v_ik_2966_, v_w_2967_);
lean_dec(v_hi_2959_);
lean_dec(v_lo_2958_);
lean_dec(v_n_2957_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(lean_object* v_as_2969_, size_t v_sz_2970_, size_t v_i_2971_, lean_object* v_b_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
lean_object* v___x_2976_; 
v___x_2976_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_2969_, v_sz_2970_, v_i_2971_, v_b_2972_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___boxed(lean_object* v_as_2977_, lean_object* v_sz_2978_, lean_object* v_i_2979_, lean_object* v_b_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
size_t v_sz_boxed_2984_; size_t v_i_boxed_2985_; lean_object* v_res_2986_; 
v_sz_boxed_2984_ = lean_unbox_usize(v_sz_2978_);
lean_dec(v_sz_2978_);
v_i_boxed_2985_ = lean_unbox_usize(v_i_2979_);
lean_dec(v_i_2979_);
v_res_2986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(v_as_2977_, v_sz_boxed_2984_, v_i_boxed_2985_, v_b_2980_, v___y_2981_, v___y_2982_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec_ref(v_as_2977_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object* v_init_2987_, lean_object* v_t_2988_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_2987_, v_t_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object* v_init_2990_, lean_object* v_t_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(v_init_2990_, v_t_2991_);
lean_dec(v_t_2991_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object* v_n_2993_, lean_object* v_as_2994_, lean_object* v_lo_2995_, lean_object* v_hi_2996_, lean_object* v_w_2997_, lean_object* v_hlo_2998_, lean_object* v_hhi_2999_){
_start:
{
lean_object* v___x_3000_; 
v___x_3000_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_2993_, v_as_2994_, v_lo_2995_, v_hi_2996_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object* v_n_3001_, lean_object* v_as_3002_, lean_object* v_lo_3003_, lean_object* v_hi_3004_, lean_object* v_w_3005_, lean_object* v_hlo_3006_, lean_object* v_hhi_3007_){
_start:
{
lean_object* v_res_3008_; 
v_res_3008_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(v_n_3001_, v_as_3002_, v_lo_3003_, v_hi_3004_, v_w_3005_, v_hlo_3006_, v_hhi_3007_);
lean_dec(v_hi_3004_);
lean_dec(v_n_3001_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object* v_init_3009_, lean_object* v_x_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
lean_object* v___x_3014_; 
v___x_3014_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_3009_, v_x_3010_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object* v_init_3015_, lean_object* v_x_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(v_init_3015_, v_x_3016_, v___y_3017_, v___y_3018_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_3021_, lean_object* v_x_3022_, size_t v_x_3023_, lean_object* v_x_3024_){
_start:
{
lean_object* v___x_3025_; 
v___x_3025_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3022_, v_x_3023_, v_x_3024_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3026_, lean_object* v_x_3027_, lean_object* v_x_3028_, lean_object* v_x_3029_){
_start:
{
size_t v_x_18970__boxed_3030_; lean_object* v_res_3031_; 
v_x_18970__boxed_3030_ = lean_unbox_usize(v_x_3028_);
lean_dec(v_x_3028_);
v_res_3031_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(v_00_u03b2_3026_, v_x_3027_, v_x_18970__boxed_3030_, v_x_3029_);
lean_dec(v_x_3029_);
lean_dec_ref(v_x_3027_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object* v_as_3032_, lean_object* v_k_3033_, lean_object* v_x_3034_, lean_object* v_x_3035_, lean_object* v_x_3036_){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_3032_, v_k_3033_, v_x_3034_, v_x_3035_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object* v_as_3038_, lean_object* v_k_3039_, lean_object* v_x_3040_, lean_object* v_x_3041_, lean_object* v_x_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(v_as_3038_, v_k_3039_, v_x_3040_, v_x_3041_, v_x_3042_);
lean_dec_ref(v_k_3039_);
lean_dec_ref(v_as_3038_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(lean_object* v_00_u03b2_3044_, lean_object* v_m_3045_, lean_object* v_a_3046_){
_start:
{
lean_object* v___x_3047_; 
v___x_3047_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_3045_, v_a_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___boxed(lean_object* v_00_u03b2_3048_, lean_object* v_m_3049_, lean_object* v_a_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(v_00_u03b2_3048_, v_m_3049_, v_a_3050_);
lean_dec(v_a_3050_);
lean_dec_ref(v_m_3049_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(lean_object* v_n_3052_, lean_object* v_lo_3053_, lean_object* v_hi_3054_, lean_object* v_hhi_3055_, lean_object* v_pivot_3056_, lean_object* v_as_3057_, lean_object* v_i_3058_, lean_object* v_k_3059_, lean_object* v_ilo_3060_, lean_object* v_ik_3061_, lean_object* v_w_3062_){
_start:
{
lean_object* v___x_3063_; 
v___x_3063_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_3054_, v_pivot_3056_, v_as_3057_, v_i_3058_, v_k_3059_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___boxed(lean_object* v_n_3064_, lean_object* v_lo_3065_, lean_object* v_hi_3066_, lean_object* v_hhi_3067_, lean_object* v_pivot_3068_, lean_object* v_as_3069_, lean_object* v_i_3070_, lean_object* v_k_3071_, lean_object* v_ilo_3072_, lean_object* v_ik_3073_, lean_object* v_w_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(v_n_3064_, v_lo_3065_, v_hi_3066_, v_hhi_3067_, v_pivot_3068_, v_as_3069_, v_i_3070_, v_k_3071_, v_ilo_3072_, v_ik_3073_, v_w_3074_);
lean_dec(v_hi_3066_);
lean_dec(v_lo_3065_);
lean_dec(v_n_3064_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_3076_, lean_object* v_keys_3077_, lean_object* v_vals_3078_, lean_object* v_heq_3079_, lean_object* v_i_3080_, lean_object* v_k_3081_){
_start:
{
lean_object* v___x_3082_; 
v___x_3082_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_3077_, v_vals_3078_, v_i_3080_, v_k_3081_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object* v_00_u03b2_3083_, lean_object* v_keys_3084_, lean_object* v_vals_3085_, lean_object* v_heq_3086_, lean_object* v_i_3087_, lean_object* v_k_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(v_00_u03b2_3083_, v_keys_3084_, v_vals_3085_, v_heq_3086_, v_i_3087_, v_k_3088_);
lean_dec(v_k_3088_);
lean_dec_ref(v_vals_3085_);
lean_dec_ref(v_keys_3084_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(lean_object* v_00_u03b2_3090_, lean_object* v_a_3091_, lean_object* v_x_3092_){
_start:
{
lean_object* v___x_3093_; 
v___x_3093_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_3091_, v_x_3092_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___boxed(lean_object* v_00_u03b2_3094_, lean_object* v_a_3095_, lean_object* v_x_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(v_00_u03b2_3094_, v_a_3095_, v_x_3096_);
lean_dec(v_x_3096_);
lean_dec(v_a_3095_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1(){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3112_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3113_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1));
v___x_3114_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3115_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed), 4, 0);
v___x_3116_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3112_, v___x_3113_, v___x_3114_, v___x_3115_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object* v_a_3117_){
_start:
{
lean_object* v_res_3118_; 
v_res_3118_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3(){
_start:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3121_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3122_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0));
v___x_3123_ = l_Lean_addBuiltinDocString(v___x_3121_, v___x_3122_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object* v_a_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5(){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3152_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3153_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6));
v___x_3154_ = l_Lean_addBuiltinDeclarationRanges(v___x_3152_, v___x_3153_);
return v___x_3154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object* v_a_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object* v_env_3157_, lean_object* v___x_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, uint8_t v_includeUnnamed_3161_, lean_object* v_x_3162_, lean_object* v_____s_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
lean_object* v_fst_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3224_; 
v_fst_3169_ = lean_ctor_get(v_x_3162_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v_x_3162_);
if (v_isSharedCheck_3224_ == 0)
{
lean_object* v_unused_3225_; 
v_unused_3225_ = lean_ctor_get(v_x_3162_, 1);
lean_dec(v_unused_3225_);
v___x_3171_ = v_x_3162_;
v_isShared_3172_ = v_isSharedCheck_3224_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_fst_3169_);
lean_dec(v_x_3162_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3224_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v_userName_3174_; lean_object* v___y_3175_; lean_object* v___x_3209_; 
lean_inc(v_fst_3169_);
lean_inc_ref(v_env_3157_);
v___x_3209_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_3157_, v_fst_3169_);
if (lean_obj_tag(v___x_3209_) == 1)
{
lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3217_; 
lean_del_object(v___x_3171_);
lean_dec(v_fst_3169_);
lean_dec(v___x_3158_);
lean_dec_ref(v_env_3157_);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3217_ == 0)
{
lean_object* v_unused_3218_; 
v_unused_3218_ = lean_ctor_get(v___x_3209_, 0);
lean_dec(v_unused_3218_);
v___x_3211_ = v___x_3209_;
v_isShared_3212_ = v_isSharedCheck_3217_;
goto v_resetjp_3210_;
}
else
{
lean_dec(v___x_3209_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3217_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 0, v_____s_3163_);
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_____s_3163_);
v___x_3214_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
lean_object* v___x_3215_; 
v___x_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
return v___x_3215_;
}
}
}
else
{
lean_object* v___x_3219_; 
lean_dec(v___x_3209_);
v___x_3219_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_a_3160_, v_fst_3169_);
if (lean_obj_tag(v___x_3219_) == 1)
{
lean_object* v_val_3220_; 
v_val_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_val_3220_);
lean_dec_ref_known(v___x_3219_, 1);
v_userName_3174_ = v_val_3220_;
v___y_3175_ = v___y_3166_;
goto v___jp_3173_;
}
else
{
lean_dec(v___x_3219_);
if (v_includeUnnamed_3161_ == 0)
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
lean_del_object(v___x_3171_);
lean_dec(v_fst_3169_);
lean_dec(v___x_3158_);
lean_dec_ref(v_env_3157_);
v___x_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3221_, 0, v_____s_3163_);
v___x_3222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
return v___x_3222_;
}
else
{
lean_object* v___x_3223_; 
lean_inc(v_fst_3169_);
v___x_3223_ = l_Lean_Name_toString(v_fst_3169_, v_includeUnnamed_3161_);
v_userName_3174_ = v___x_3223_;
v___y_3175_ = v___y_3166_;
goto v___jp_3173_;
}
}
}
v___jp_3173_:
{
lean_object* v_ref_3176_; uint8_t v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v_ref_3176_ = lean_ctor_get(v___y_3175_, 2);
v___x_3177_ = 1;
v___x_3178_ = l_Lean_Options_empty;
v___x_3179_ = lean_box(0);
lean_inc(v_fst_3169_);
lean_inc_ref(v_env_3157_);
v___x_3180_ = l_Lean_findDocString_x3f(v_env_3157_, v_fst_3169_, v___x_3177_, v___x_3178_, v___x_3158_, v___x_3179_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3194_; 
lean_del_object(v___x_3171_);
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3183_ = v___x_3180_;
v_isShared_3184_ = v_isSharedCheck_3194_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3180_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3194_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3192_; 
v___x_3185_ = l_Lean_NameSet_empty;
v___x_3186_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_a_3159_, v_fst_3169_, v___x_3185_);
lean_inc(v_fst_3169_);
v___x_3187_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_3157_, v_fst_3169_);
v___x_3188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3188_, 0, v_fst_3169_);
lean_ctor_set(v___x_3188_, 1, v_userName_3174_);
lean_ctor_set(v___x_3188_, 2, v___x_3186_);
lean_ctor_set(v___x_3188_, 3, v_a_3181_);
lean_ctor_set(v___x_3188_, 4, v___x_3187_);
v___x_3189_ = lean_array_push(v_____s_3163_, v___x_3188_);
v___x_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 0, v___x_3190_);
v___x_3192_ = v___x_3183_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3190_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
else
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3208_; 
lean_dec_ref(v_userName_3174_);
lean_dec(v_fst_3169_);
lean_dec_ref(v_____s_3163_);
lean_dec_ref(v_env_3157_);
v_a_3195_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3197_ = v___x_3180_;
v_isShared_3198_ = v_isSharedCheck_3208_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3180_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3208_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3203_; 
v___x_3199_ = lean_io_error_to_string(v_a_3195_);
v___x_3200_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3199_);
v___x_3201_ = l_Lean_MessageData_ofFormat(v___x_3200_);
lean_inc(v_ref_3176_);
if (v_isShared_3172_ == 0)
{
lean_ctor_set(v___x_3171_, 1, v___x_3201_);
lean_ctor_set(v___x_3171_, 0, v_ref_3176_);
v___x_3203_ = v___x_3171_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_ref_3176_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v___x_3201_);
v___x_3203_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
lean_object* v___x_3205_; 
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 0, v___x_3203_);
v___x_3205_ = v___x_3197_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3203_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object* v_env_3226_, lean_object* v___x_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_includeUnnamed_3230_, lean_object* v_x_3231_, lean_object* v_____s_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
uint8_t v_includeUnnamed_boxed_3238_; lean_object* v_res_3239_; 
v_includeUnnamed_boxed_3238_ = lean_unbox(v_includeUnnamed_3230_);
v_res_3239_ = l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(v_env_3226_, v___x_3227_, v_a_3228_, v_a_3229_, v_includeUnnamed_boxed_3238_, v_x_3231_, v_____s_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v_a_3229_);
lean_dec(v_a_3228_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object* v_as_3240_, size_t v_sz_3241_, size_t v_i_3242_, lean_object* v_b_3243_){
_start:
{
uint8_t v___x_3245_; 
v___x_3245_ = lean_usize_dec_lt(v_i_3242_, v_sz_3241_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3246_; 
v___x_3246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3246_, 0, v_b_3243_);
return v___x_3246_;
}
else
{
lean_object* v_a_3247_; lean_object* v_fst_3248_; lean_object* v_snd_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; size_t v___x_3254_; size_t v___x_3255_; 
v_a_3247_ = lean_array_uget_borrowed(v_as_3240_, v_i_3242_);
v_fst_3248_ = lean_ctor_get(v_a_3247_, 0);
v_snd_3249_ = lean_ctor_get(v_a_3247_, 1);
v___x_3250_ = l_Lean_NameSet_empty;
v___x_3251_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_3243_, v_fst_3248_, v___x_3250_);
lean_inc(v_snd_3249_);
v___x_3252_ = l_Lean_NameSet_insert(v___x_3251_, v_snd_3249_);
lean_inc(v_fst_3248_);
v___x_3253_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3248_, v___x_3252_, v_b_3243_);
v___x_3254_ = ((size_t)1ULL);
v___x_3255_ = lean_usize_add(v_i_3242_, v___x_3254_);
v_i_3242_ = v___x_3255_;
v_b_3243_ = v___x_3253_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object* v_as_3257_, lean_object* v_sz_3258_, lean_object* v_i_3259_, lean_object* v_b_3260_, lean_object* v___y_3261_){
_start:
{
size_t v_sz_boxed_3262_; size_t v_i_boxed_3263_; lean_object* v_res_3264_; 
v_sz_boxed_3262_ = lean_unbox_usize(v_sz_3258_);
lean_dec(v_sz_3258_);
v_i_boxed_3263_ = lean_unbox_usize(v_i_3259_);
lean_dec(v_i_3259_);
v_res_3264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_3257_, v_sz_boxed_3262_, v_i_boxed_3263_, v_b_3260_);
lean_dec_ref(v_as_3257_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object* v_as_3265_, size_t v_sz_3266_, size_t v_i_3267_, lean_object* v_b_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
uint8_t v___x_3274_; 
v___x_3274_ = lean_usize_dec_lt(v_i_3267_, v_sz_3266_);
if (v___x_3274_ == 0)
{
lean_object* v___x_3275_; 
v___x_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3275_, 0, v_b_3268_);
return v___x_3275_;
}
else
{
lean_object* v_a_3276_; size_t v_sz_3277_; size_t v___x_3278_; lean_object* v___x_3279_; 
v_a_3276_ = lean_array_uget_borrowed(v_as_3265_, v_i_3267_);
v_sz_3277_ = lean_array_size(v_a_3276_);
v___x_3278_ = ((size_t)0ULL);
v___x_3279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_a_3276_, v_sz_3277_, v___x_3278_, v_b_3268_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v_a_3280_; size_t v___x_3281_; size_t v___x_3282_; 
v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
lean_inc(v_a_3280_);
lean_dec_ref_known(v___x_3279_, 1);
v___x_3281_ = ((size_t)1ULL);
v___x_3282_ = lean_usize_add(v_i_3267_, v___x_3281_);
v_i_3267_ = v___x_3282_;
v_b_3268_ = v_a_3280_;
goto _start;
}
else
{
return v___x_3279_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object* v_as_3284_, lean_object* v_sz_3285_, lean_object* v_i_3286_, lean_object* v_b_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
size_t v_sz_boxed_3293_; size_t v_i_boxed_3294_; lean_object* v_res_3295_; 
v_sz_boxed_3293_ = lean_unbox_usize(v_sz_3285_);
lean_dec(v_sz_3285_);
v_i_boxed_3294_ = lean_unbox_usize(v_i_3286_);
lean_dec(v_i_3286_);
v_res_3295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v_as_3284_, v_sz_boxed_3293_, v_i_boxed_3294_, v_b_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec_ref(v_as_3284_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object* v_f_3296_, lean_object* v_keys_3297_, lean_object* v_vals_3298_, lean_object* v_i_3299_, lean_object* v_acc_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
lean_object* v___x_3306_; uint8_t v___x_3307_; 
v___x_3306_ = lean_array_get_size(v_keys_3297_);
v___x_3307_ = lean_nat_dec_lt(v_i_3299_, v___x_3306_);
if (v___x_3307_ == 0)
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
lean_dec(v_i_3299_);
lean_dec_ref(v_f_3296_);
v___x_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3308_, 0, v_acc_3300_);
v___x_3309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3308_);
return v___x_3309_;
}
else
{
lean_object* v_k_3310_; lean_object* v_v_3311_; lean_object* v___x_3312_; 
v_k_3310_ = lean_array_fget_borrowed(v_keys_3297_, v_i_3299_);
v_v_3311_ = lean_array_fget_borrowed(v_vals_3298_, v_i_3299_);
lean_inc_ref(v_f_3296_);
lean_inc(v___y_3304_);
lean_inc_ref(v___y_3303_);
lean_inc(v___y_3302_);
lean_inc_ref(v___y_3301_);
lean_inc(v_v_3311_);
lean_inc(v_k_3310_);
v___x_3312_ = lean_apply_8(v_f_3296_, v_acc_3300_, v_k_3310_, v_v_3311_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, lean_box(0));
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_object* v_a_3313_; 
v_a_3313_ = lean_ctor_get(v___x_3312_, 0);
lean_inc(v_a_3313_);
if (lean_obj_tag(v_a_3313_) == 0)
{
lean_dec_ref_known(v_a_3313_, 1);
lean_dec(v_i_3299_);
lean_dec_ref(v_f_3296_);
return v___x_3312_;
}
else
{
lean_object* v_a_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
lean_dec_ref_known(v___x_3312_, 1);
v_a_3314_ = lean_ctor_get(v_a_3313_, 0);
lean_inc(v_a_3314_);
lean_dec_ref_known(v_a_3313_, 1);
v___x_3315_ = lean_unsigned_to_nat(1u);
v___x_3316_ = lean_nat_add(v_i_3299_, v___x_3315_);
lean_dec(v_i_3299_);
v_i_3299_ = v___x_3316_;
v_acc_3300_ = v_a_3314_;
goto _start;
}
}
else
{
lean_dec(v_i_3299_);
lean_dec_ref(v_f_3296_);
return v___x_3312_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_f_3318_, lean_object* v_keys_3319_, lean_object* v_vals_3320_, lean_object* v_i_3321_, lean_object* v_acc_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3318_, v_keys_3319_, v_vals_3320_, v_i_3321_, v_acc_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_);
lean_dec(v___y_3326_);
lean_dec_ref(v___y_3325_);
lean_dec(v___y_3324_);
lean_dec_ref(v___y_3323_);
lean_dec_ref(v_vals_3320_);
lean_dec_ref(v_keys_3319_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_f_3329_, lean_object* v_as_3330_, size_t v_i_3331_, size_t v_stop_3332_, lean_object* v_b_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
lean_object* v_a_3340_; lean_object* v___y_3345_; uint8_t v___x_3348_; 
v___x_3348_ = lean_usize_dec_eq(v_i_3331_, v_stop_3332_);
if (v___x_3348_ == 0)
{
lean_object* v___x_3349_; 
v___x_3349_ = lean_array_uget_borrowed(v_as_3330_, v_i_3331_);
switch(lean_obj_tag(v___x_3349_))
{
case 0:
{
lean_object* v_key_3350_; lean_object* v_val_3351_; lean_object* v___x_3352_; 
v_key_3350_ = lean_ctor_get(v___x_3349_, 0);
v_val_3351_ = lean_ctor_get(v___x_3349_, 1);
lean_inc_ref(v_f_3329_);
lean_inc(v___y_3337_);
lean_inc_ref(v___y_3336_);
lean_inc(v___y_3335_);
lean_inc_ref(v___y_3334_);
lean_inc(v_val_3351_);
lean_inc(v_key_3350_);
v___x_3352_ = lean_apply_8(v_f_3329_, v_b_3333_, v_key_3350_, v_val_3351_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, lean_box(0));
v___y_3345_ = v___x_3352_;
goto v___jp_3344_;
}
case 1:
{
lean_object* v_node_3353_; lean_object* v___x_3354_; 
v_node_3353_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_node_3353_);
lean_inc_ref(v_f_3329_);
v___x_3354_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3329_, v_node_3353_, v_b_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
v___y_3345_ = v___x_3354_;
goto v___jp_3344_;
}
default: 
{
v_a_3340_ = v_b_3333_;
goto v___jp_3339_;
}
}
}
else
{
lean_object* v___x_3355_; lean_object* v___x_3356_; 
lean_dec_ref(v_f_3329_);
v___x_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3355_, 0, v_b_3333_);
v___x_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3355_);
return v___x_3356_;
}
v___jp_3339_:
{
size_t v___x_3341_; size_t v___x_3342_; 
v___x_3341_ = ((size_t)1ULL);
v___x_3342_ = lean_usize_add(v_i_3331_, v___x_3341_);
v_i_3331_ = v___x_3342_;
v_b_3333_ = v_a_3340_;
goto _start;
}
v___jp_3344_:
{
if (lean_obj_tag(v___y_3345_) == 0)
{
lean_object* v_a_3346_; 
v_a_3346_ = lean_ctor_get(v___y_3345_, 0);
if (lean_obj_tag(v_a_3346_) == 0)
{
lean_dec_ref(v_f_3329_);
return v___y_3345_;
}
else
{
lean_object* v_a_3347_; 
lean_inc_ref(v_a_3346_);
lean_dec_ref_known(v___y_3345_, 1);
v_a_3347_ = lean_ctor_get(v_a_3346_, 0);
lean_inc(v_a_3347_);
lean_dec_ref_known(v_a_3346_, 1);
v_a_3340_ = v_a_3347_;
goto v___jp_3339_;
}
}
else
{
lean_dec_ref(v_f_3329_);
return v___y_3345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object* v_f_3357_, lean_object* v_x_3358_, lean_object* v_x_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
if (lean_obj_tag(v_x_3358_) == 0)
{
lean_object* v_es_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3379_; 
v_es_3365_ = lean_ctor_get(v_x_3358_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v_x_3358_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3367_ = v_x_3358_;
v_isShared_3368_ = v_isSharedCheck_3379_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_es_3365_);
lean_dec(v_x_3358_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3379_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; uint8_t v___x_3371_; 
v___x_3369_ = lean_unsigned_to_nat(0u);
v___x_3370_ = lean_array_get_size(v_es_3365_);
v___x_3371_ = lean_nat_dec_lt(v___x_3369_, v___x_3370_);
if (v___x_3371_ == 0)
{
lean_object* v___x_3373_; 
lean_dec_ref(v_es_3365_);
lean_dec_ref(v_f_3357_);
if (v_isShared_3368_ == 0)
{
lean_ctor_set_tag(v___x_3367_, 1);
lean_ctor_set(v___x_3367_, 0, v_x_3359_);
v___x_3373_ = v___x_3367_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_x_3359_);
v___x_3373_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
lean_object* v___x_3374_; 
v___x_3374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3373_);
return v___x_3374_;
}
}
else
{
size_t v___x_3376_; size_t v___x_3377_; lean_object* v___x_3378_; 
lean_del_object(v___x_3367_);
v___x_3376_ = ((size_t)0ULL);
v___x_3377_ = lean_usize_of_nat(v___x_3370_);
v___x_3378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3357_, v_es_3365_, v___x_3376_, v___x_3377_, v_x_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
lean_dec_ref(v_es_3365_);
return v___x_3378_;
}
}
}
else
{
lean_object* v_ks_3380_; lean_object* v_vs_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
v_ks_3380_ = lean_ctor_get(v_x_3358_, 0);
lean_inc_ref(v_ks_3380_);
v_vs_3381_ = lean_ctor_get(v_x_3358_, 1);
lean_inc_ref(v_vs_3381_);
lean_dec_ref_known(v_x_3358_, 2);
v___x_3382_ = lean_unsigned_to_nat(0u);
v___x_3383_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3357_, v_ks_3380_, v_vs_3381_, v___x_3382_, v_x_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
lean_dec_ref(v_vs_3381_);
lean_dec_ref(v_ks_3380_);
return v___x_3383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_f_3384_, lean_object* v_x_3385_, lean_object* v_x_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3384_, v_x_3385_, v_x_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_3393_, lean_object* v_as_3394_, lean_object* v_i_3395_, lean_object* v_stop_3396_, lean_object* v_b_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
size_t v_i_boxed_3403_; size_t v_stop_boxed_3404_; lean_object* v_res_3405_; 
v_i_boxed_3403_ = lean_unbox_usize(v_i_3395_);
lean_dec(v_i_3395_);
v_stop_boxed_3404_ = lean_unbox_usize(v_stop_3396_);
lean_dec(v_stop_3396_);
v_res_3405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3393_, v_as_3394_, v_i_boxed_3403_, v_stop_boxed_3404_, v_b_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec_ref(v_as_3394_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object* v_f_3406_, lean_object* v_s_3407_, lean_object* v_a_3408_, lean_object* v_b_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3415_, 0, v_a_3408_);
lean_ctor_set(v___x_3415_, 1, v_b_3409_);
lean_inc(v___y_3413_);
lean_inc_ref(v___y_3412_);
lean_inc(v___y_3411_);
lean_inc_ref(v___y_3410_);
v___x_3416_ = lean_apply_7(v_f_3406_, v___x_3415_, v_s_3407_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, lean_box(0));
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3443_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3419_ = v___x_3416_;
v_isShared_3420_ = v_isSharedCheck_3443_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3416_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3443_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
if (lean_obj_tag(v_a_3417_) == 0)
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3431_; 
v_a_3421_ = lean_ctor_get(v_a_3417_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v_a_3417_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3423_ = v_a_3417_;
v_isShared_3424_ = v_isSharedCheck_3431_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v_a_3417_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3431_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3424_ == 0)
{
v___x_3426_ = v___x_3423_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3421_);
v___x_3426_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
lean_object* v___x_3428_; 
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v___x_3426_);
v___x_3428_ = v___x_3419_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3426_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
else
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3442_; 
v_a_3432_ = lean_ctor_get(v_a_3417_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v_a_3417_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3434_ = v_a_3417_;
v_isShared_3435_ = v_isSharedCheck_3442_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v_a_3417_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3442_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3432_);
v___x_3437_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
lean_object* v___x_3439_; 
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v___x_3437_);
v___x_3439_ = v___x_3419_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3437_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
}
}
else
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
v_a_3444_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_3416_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3416_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3444_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object* v_f_3452_, lean_object* v_s_3453_, lean_object* v_a_3454_, lean_object* v_b_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(v_f_3452_, v_s_3453_, v_a_3454_, v_b_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object* v_map_3462_, lean_object* v_init_3463_, lean_object* v_f_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_){
_start:
{
lean_object* v___f_3470_; lean_object* v___x_3471_; 
v___f_3470_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3470_, 0, v_f_3464_);
lean_inc_ref(v_map_3462_);
v___x_3471_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v___f_3470_, v_map_3462_, v_init_3463_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3480_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3474_ = v___x_3471_;
v_isShared_3475_ = v_isSharedCheck_3480_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3471_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3480_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v_a_3476_; lean_object* v___x_3478_; 
v_a_3476_ = lean_ctor_get(v_a_3472_, 0);
lean_inc(v_a_3476_);
lean_dec(v_a_3472_);
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 0, v_a_3476_);
v___x_3478_ = v___x_3474_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3476_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
else
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3488_; 
v_a_3481_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3483_ = v___x_3471_;
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3471_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3486_; 
if (v_isShared_3484_ == 0)
{
v___x_3486_ = v___x_3483_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3481_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object* v_map_3489_, lean_object* v_init_3490_, lean_object* v_f_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_3489_, v_init_3490_, v_f_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec_ref(v_map_3489_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object* v___y_3498_){
_start:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v_env_3504_; lean_object* v___x_3505_; lean_object* v_ext_3506_; lean_object* v_toEnvExtension_3507_; lean_object* v_asyncMode_3508_; lean_object* v___x_3509_; lean_object* v_categories_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3500_ = lean_box(1);
v___x_3501_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3502_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3503_ = lean_st_ref_get(v___y_3498_);
v_env_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc_ref_n(v_env_3504_, 2);
lean_dec(v___x_3503_);
v___x_3505_ = l_Lean_Parser_parserExtension;
v_ext_3506_ = lean_ctor_get(v___x_3505_, 1);
v_toEnvExtension_3507_ = lean_ctor_get(v_ext_3506_, 0);
v_asyncMode_3508_ = lean_ctor_get(v_toEnvExtension_3507_, 2);
v___x_3509_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3502_, v___x_3505_, v_env_3504_, v_asyncMode_3508_);
v_categories_3510_ = lean_ctor_get(v___x_3509_, 2);
lean_inc_ref(v_categories_3510_);
lean_dec(v___x_3509_);
v___x_3511_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3512_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3510_, v___x_3511_);
lean_dec_ref(v_categories_3510_);
if (lean_obj_tag(v___x_3512_) == 1)
{
lean_object* v_val_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3544_; 
v_val_3513_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3515_ = v___x_3512_;
v_isShared_3516_ = v_isSharedCheck_3544_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_val_3513_);
lean_dec(v___x_3512_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3544_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___y_3518_; lean_object* v___x_3527_; lean_object* v_toEnvExtension_3528_; lean_object* v_exportEntriesFn_3529_; lean_object* v_asyncMode_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v_importedEntries_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v_exported_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; uint8_t v___x_3540_; 
v___x_3527_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3528_ = lean_ctor_get(v___x_3527_, 0);
v_exportEntriesFn_3529_ = lean_ctor_get(v___x_3527_, 4);
v_asyncMode_3530_ = lean_ctor_get(v_toEnvExtension_3528_, 2);
v___x_3531_ = lean_box(0);
lean_inc_ref_n(v_env_3504_, 2);
v___x_3532_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3501_, v_toEnvExtension_3528_, v_env_3504_, v_asyncMode_3530_, v___x_3531_);
v_importedEntries_3533_ = lean_ctor_get(v___x_3532_, 0);
lean_inc_ref(v_importedEntries_3533_);
lean_dec(v___x_3532_);
v___x_3534_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3500_, v___x_3527_, v_env_3504_, v_asyncMode_3530_, v___x_3531_);
lean_inc_ref(v_exportEntriesFn_3529_);
v___x_3535_ = lean_apply_2(v_exportEntriesFn_3529_, v_env_3504_, v___x_3534_);
v_exported_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_exported_3536_);
lean_dec_ref(v___x_3535_);
v___x_3537_ = lean_array_push(v_importedEntries_3533_, v_exported_3536_);
v___x_3538_ = lean_unsigned_to_nat(0u);
v___x_3539_ = lean_array_get_size(v___x_3537_);
v___x_3540_ = lean_nat_dec_lt(v___x_3538_, v___x_3539_);
if (v___x_3540_ == 0)
{
lean_dec_ref(v___x_3537_);
v___y_3518_ = v___x_3500_;
goto v___jp_3517_;
}
else
{
size_t v___x_3541_; size_t v___x_3542_; lean_object* v___x_3543_; 
v___x_3541_ = ((size_t)0ULL);
v___x_3542_ = lean_usize_of_nat(v___x_3539_);
v___x_3543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3537_, v___x_3541_, v___x_3542_, v___x_3500_);
lean_dec_ref(v___x_3537_);
v___y_3518_ = v___x_3543_;
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
lean_object* v___x_3545_; 
lean_dec(v___x_3512_);
lean_dec_ref(v_env_3504_);
v___x_3545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3500_);
return v___x_3545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v_res_3548_; 
v_res_3548_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_3546_);
lean_dec(v___y_3546_);
return v_res_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t v_includeUnnamed_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v_env_3561_; lean_object* v___x_3562_; lean_object* v_toEnvExtension_3563_; lean_object* v_exportEntriesFn_3564_; lean_object* v_asyncMode_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v_importedEntries_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v_exported_3571_; lean_object* v___x_3572_; size_t v_sz_3573_; size_t v___x_3574_; lean_object* v___x_3575_; 
v___x_3557_ = lean_box(1);
v___x_3558_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3559_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3560_ = lean_st_ref_get(v_a_3555_);
v_env_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc_ref_n(v_env_3561_, 4);
lean_dec(v___x_3560_);
v___x_3562_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_3563_ = lean_ctor_get(v___x_3562_, 0);
v_exportEntriesFn_3564_ = lean_ctor_get(v___x_3562_, 4);
v_asyncMode_3565_ = lean_ctor_get(v_toEnvExtension_3563_, 2);
v___x_3566_ = lean_box(0);
v___x_3567_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3558_, v_toEnvExtension_3563_, v_env_3561_, v_asyncMode_3565_, v___x_3566_);
v_importedEntries_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc_ref(v_importedEntries_3568_);
lean_dec(v___x_3567_);
v___x_3569_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3557_, v___x_3562_, v_env_3561_, v_asyncMode_3565_, v___x_3566_);
lean_inc_ref(v_exportEntriesFn_3564_);
v___x_3570_ = lean_apply_2(v_exportEntriesFn_3564_, v_env_3561_, v___x_3569_);
v_exported_3571_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_exported_3571_);
lean_dec_ref(v___x_3570_);
v___x_3572_ = lean_array_push(v_importedEntries_3568_, v_exported_3571_);
v_sz_3573_ = lean_array_size(v___x_3572_);
v___x_3574_ = ((size_t)0ULL);
v___x_3575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v___x_3572_, v_sz_3573_, v___x_3574_, v___x_3557_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_);
lean_dec_ref(v___x_3572_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3599_; 
v_a_3576_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3578_ = v___x_3575_;
v_isShared_3579_ = v_isSharedCheck_3599_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3575_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3599_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3580_; lean_object* v_ext_3581_; lean_object* v_toEnvExtension_3582_; lean_object* v_asyncMode_3583_; lean_object* v___x_3584_; lean_object* v_categories_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3580_ = l_Lean_Parser_parserExtension;
v_ext_3581_ = lean_ctor_get(v___x_3580_, 1);
v_toEnvExtension_3582_ = lean_ctor_get(v_ext_3581_, 0);
v_asyncMode_3583_ = lean_ctor_get(v_toEnvExtension_3582_, 2);
lean_inc_ref(v_env_3561_);
v___x_3584_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3559_, v___x_3580_, v_env_3561_, v_asyncMode_3583_);
v_categories_3585_ = lean_ctor_get(v___x_3584_, 2);
lean_inc_ref(v_categories_3585_);
lean_dec(v___x_3584_);
v___x_3586_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0));
v___x_3587_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3588_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3585_, v___x_3587_);
lean_dec_ref(v_categories_3585_);
if (lean_obj_tag(v___x_3588_) == 1)
{
lean_object* v_val_3589_; lean_object* v___x_3590_; lean_object* v_a_3591_; lean_object* v_kinds_3592_; lean_object* v___x_3593_; lean_object* v___f_3594_; lean_object* v___x_3595_; 
lean_del_object(v___x_3578_);
v_val_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_val_3589_);
lean_dec_ref_known(v___x_3588_, 1);
v___x_3590_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v_a_3555_);
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
lean_inc(v_a_3591_);
lean_dec_ref(v___x_3590_);
v_kinds_3592_ = lean_ctor_get(v_val_3589_, 1);
lean_inc_ref(v_kinds_3592_);
lean_dec(v_val_3589_);
v___x_3593_ = lean_box(v_includeUnnamed_3551_);
v___f_3594_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed), 12, 5);
lean_closure_set(v___f_3594_, 0, v_env_3561_);
lean_closure_set(v___f_3594_, 1, v___x_3566_);
lean_closure_set(v___f_3594_, 2, v_a_3576_);
lean_closure_set(v___f_3594_, 3, v_a_3591_);
lean_closure_set(v___f_3594_, 4, v___x_3593_);
v___x_3595_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_kinds_3592_, v___x_3586_, v___f_3594_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_);
lean_dec_ref(v_kinds_3592_);
return v___x_3595_;
}
else
{
lean_object* v___x_3597_; 
lean_dec(v___x_3588_);
lean_dec(v_a_3576_);
lean_dec_ref(v_env_3561_);
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 0, v___x_3586_);
v___x_3597_ = v___x_3578_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v___x_3586_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3607_; 
lean_dec_ref(v_env_3561_);
v_a_3600_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3602_ = v___x_3575_;
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3575_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3605_; 
if (v_isShared_3603_ == 0)
{
v___x_3605_ = v___x_3602_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3600_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object* v_includeUnnamed_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_){
_start:
{
uint8_t v_includeUnnamed_boxed_3614_; lean_object* v_res_3615_; 
v_includeUnnamed_boxed_3614_ = lean_unbox(v_includeUnnamed_3608_);
v_res_3615_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v_includeUnnamed_boxed_3614_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_);
lean_dec(v_a_3612_);
lean_dec_ref(v_a_3611_);
lean_dec(v_a_3610_);
lean_dec_ref(v_a_3609_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object* v_as_3616_, size_t v_sz_3617_, size_t v_i_3618_, lean_object* v_b_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v___x_3625_; 
v___x_3625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_3616_, v_sz_3617_, v_i_3618_, v_b_3619_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object* v_as_3626_, lean_object* v_sz_3627_, lean_object* v_i_3628_, lean_object* v_b_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
size_t v_sz_boxed_3635_; size_t v_i_boxed_3636_; lean_object* v_res_3637_; 
v_sz_boxed_3635_ = lean_unbox_usize(v_sz_3627_);
lean_dec(v_sz_3627_);
v_i_boxed_3636_ = lean_unbox_usize(v_i_3628_);
lean_dec(v_i_3628_);
v_res_3637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(v_as_3626_, v_sz_boxed_3635_, v_i_boxed_3636_, v_b_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
lean_dec_ref(v_as_3626_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
lean_object* v___x_3643_; 
v___x_3643_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_3641_);
return v___x_3643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
return v_res_3649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object* v_00_u03c3_3650_, lean_object* v_00_u03b2_3651_, lean_object* v_map_3652_, lean_object* v_init_3653_, lean_object* v_f_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
lean_object* v___x_3660_; 
v___x_3660_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_3652_, v_init_3653_, v_f_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object* v_00_u03c3_3661_, lean_object* v_00_u03b2_3662_, lean_object* v_map_3663_, lean_object* v_init_3664_, lean_object* v_f_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(v_00_u03c3_3661_, v_00_u03b2_3662_, v_map_3663_, v_init_3664_, v_f_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec(v___y_3667_);
lean_dec_ref(v___y_3666_);
lean_dec_ref(v_map_3663_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object* v_map_3672_, lean_object* v_f_3673_, lean_object* v_init_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_){
_start:
{
lean_object* v___x_3680_; 
v___x_3680_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3673_, v_map_3672_, v_init_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
return v___x_3680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object* v_map_3681_, lean_object* v_f_3682_, lean_object* v_init_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(v_map_3681_, v_f_3682_, v_init_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
return v_res_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object* v_00_u03c3_3690_, lean_object* v_00_u03c3_3691_, lean_object* v_00_u03b2_3692_, lean_object* v_map_3693_, lean_object* v_f_3694_, lean_object* v_init_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
lean_object* v___x_3701_; 
v___x_3701_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3694_, v_map_3693_, v_init_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object* v_00_u03c3_3702_, lean_object* v_00_u03c3_3703_, lean_object* v_00_u03b2_3704_, lean_object* v_map_3705_, lean_object* v_f_3706_, lean_object* v_init_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(v_00_u03c3_3702_, v_00_u03c3_3703_, v_00_u03b2_3704_, v_map_3705_, v_f_3706_, v_init_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object* v_00_u03c3_3714_, lean_object* v_00_u03c3_3715_, lean_object* v_00_u03b1_3716_, lean_object* v_00_u03b2_3717_, lean_object* v_f_3718_, lean_object* v_x_3719_, lean_object* v_x_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_){
_start:
{
lean_object* v___x_3726_; 
v___x_3726_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3718_, v_x_3719_, v_x_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
return v___x_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03c3_3727_, lean_object* v_00_u03c3_3728_, lean_object* v_00_u03b1_3729_, lean_object* v_00_u03b2_3730_, lean_object* v_f_3731_, lean_object* v_x_3732_, lean_object* v_x_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_){
_start:
{
lean_object* v_res_3739_; 
v_res_3739_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(v_00_u03c3_3727_, v_00_u03c3_3728_, v_00_u03b1_3729_, v_00_u03b2_3730_, v_f_3731_, v_x_3732_, v_x_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_3740_, lean_object* v_00_u03b2_3741_, lean_object* v_00_u03c3_3742_, lean_object* v_00_u03c3_3743_, lean_object* v_f_3744_, lean_object* v_as_3745_, size_t v_i_3746_, size_t v_stop_3747_, lean_object* v_b_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v___x_3754_; 
v___x_3754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3744_, v_as_3745_, v_i_3746_, v_stop_3747_, v_b_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_3755_, lean_object* v_00_u03b2_3756_, lean_object* v_00_u03c3_3757_, lean_object* v_00_u03c3_3758_, lean_object* v_f_3759_, lean_object* v_as_3760_, lean_object* v_i_3761_, lean_object* v_stop_3762_, lean_object* v_b_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
size_t v_i_boxed_3769_; size_t v_stop_boxed_3770_; lean_object* v_res_3771_; 
v_i_boxed_3769_ = lean_unbox_usize(v_i_3761_);
lean_dec(v_i_3761_);
v_stop_boxed_3770_ = lean_unbox_usize(v_stop_3762_);
lean_dec(v_stop_3762_);
v_res_3771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_3755_, v_00_u03b2_3756_, v_00_u03c3_3757_, v_00_u03c3_3758_, v_f_3759_, v_as_3760_, v_i_boxed_3769_, v_stop_boxed_3770_, v_b_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
lean_dec_ref(v_as_3760_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object* v_00_u03c3_3772_, lean_object* v_00_u03c3_3773_, lean_object* v_00_u03b1_3774_, lean_object* v_00_u03b2_3775_, lean_object* v_f_3776_, lean_object* v_keys_3777_, lean_object* v_vals_3778_, lean_object* v_heq_3779_, lean_object* v_i_3780_, lean_object* v_acc_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
lean_object* v___x_3787_; 
v___x_3787_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3776_, v_keys_3777_, v_vals_3778_, v_i_3780_, v_acc_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
return v___x_3787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03c3_3788_, lean_object* v_00_u03c3_3789_, lean_object* v_00_u03b1_3790_, lean_object* v_00_u03b2_3791_, lean_object* v_f_3792_, lean_object* v_keys_3793_, lean_object* v_vals_3794_, lean_object* v_heq_3795_, lean_object* v_i_3796_, lean_object* v_acc_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(v_00_u03c3_3788_, v_00_u03c3_3789_, v_00_u03b1_3790_, v_00_u03b2_3791_, v_f_3792_, v_keys_3793_, v_vals_3794_, v_heq_3795_, v_i_3796_, v_acc_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
lean_dec(v___y_3801_);
lean_dec_ref(v___y_3800_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec_ref(v_vals_3794_);
lean_dec_ref(v_keys_3793_);
return v_res_3803_;
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
