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
lean_object* v_docs_262_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; uint8_t v___y_301_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_317_; 
v_docs_262_ = l_Lean_Syntax_getArg(v___x_256_, v___x_255_);
lean_dec(v___x_256_);
if (v___x_257_ == 0)
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16));
lean_inc(v_docs_262_);
v___x_351_ = l_Lean_Syntax_isOfKind(v_docs_262_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; 
lean_dec(v_docs_262_);
lean_dec(v_x_247_);
v___x_352_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_353_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_352_, v_a_248_, v_a_249_);
return v___x_353_;
}
else
{
goto v___jp_343_;
}
}
else
{
goto v___jp_343_;
}
v___jp_263_:
{
lean_object* v___x_266_; lean_object* v_env_267_; lean_object* v_messages_268_; lean_object* v_scopes_269_; lean_object* v_usedQuotCtxts_270_; lean_object* v_nextMacroScope_271_; lean_object* v_maxRecDepth_272_; lean_object* v_ngen_273_; lean_object* v_auxDeclNGen_274_; lean_object* v_infoState_275_; lean_object* v_traceState_276_; lean_object* v_snapshotTasks_277_; lean_object* v_prevLinterStates_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_295_; 
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
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_295_ == 0)
{
v___x_280_ = v___x_266_;
v_isShared_281_ = v_isSharedCheck_295_;
goto v_resetjp_279_;
}
else
{
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
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_295_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v_toEnvExtension_283_; lean_object* v_asyncMode_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_282_ = l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
v_toEnvExtension_283_ = lean_ctor_get(v___x_282_, 0);
v_asyncMode_284_ = lean_ctor_get(v_toEnvExtension_283_, 2);
v___x_285_ = l_Lean_TSyntax_getDocString(v_docs_262_);
lean_dec(v_docs_262_);
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___y_264_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_box(0);
v___x_288_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_282_, v_env_267_, v___x_286_, v_asyncMode_284_, v___x_287_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_288_);
v___x_290_ = v___x_280_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_messages_268_);
lean_ctor_set(v_reuseFailAlloc_294_, 2, v_scopes_269_);
lean_ctor_set(v_reuseFailAlloc_294_, 3, v_usedQuotCtxts_270_);
lean_ctor_set(v_reuseFailAlloc_294_, 4, v_nextMacroScope_271_);
lean_ctor_set(v_reuseFailAlloc_294_, 5, v_maxRecDepth_272_);
lean_ctor_set(v_reuseFailAlloc_294_, 6, v_ngen_273_);
lean_ctor_set(v_reuseFailAlloc_294_, 7, v_auxDeclNGen_274_);
lean_ctor_set(v_reuseFailAlloc_294_, 8, v_infoState_275_);
lean_ctor_set(v_reuseFailAlloc_294_, 9, v_traceState_276_);
lean_ctor_set(v_reuseFailAlloc_294_, 10, v_snapshotTasks_277_);
lean_ctor_set(v_reuseFailAlloc_294_, 11, v_prevLinterStates_278_);
v___x_290_ = v_reuseFailAlloc_294_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = lean_st_ref_put(v___y_265_, v___x_290_);
v___x_292_ = lean_box(0);
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
return v___x_293_;
}
}
}
v___jp_296_:
{
if (v___y_301_ == 0)
{
lean_dec(v___y_298_);
v___y_264_ = v___y_299_;
v___y_265_ = v___y_300_;
goto v___jp_263_;
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec(v_docs_262_);
v___x_302_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8);
v___x_303_ = l_Lean_MessageData_ofConstName(v___y_299_, v___x_257_);
v___x_304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_302_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10);
v___x_306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_304_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v___y_298_, v___x_306_, v___y_297_, v___y_300_);
lean_dec(v___y_298_);
return v___x_307_;
}
}
v___jp_308_:
{
lean_object* v___x_313_; lean_object* v_env_314_; uint8_t v___x_315_; 
v___x_313_ = lean_st_ref_get(v___y_312_);
v_env_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc_ref(v_env_314_);
lean_dec(v___x_313_);
v___x_315_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_314_, v___y_310_);
if (v___x_315_ == 0)
{
v___y_297_ = v___y_311_;
v___y_298_ = v___y_309_;
v___y_299_ = v___y_310_;
v___y_300_ = v___y_312_;
v___y_301_ = v___x_259_;
goto v___jp_296_;
}
else
{
v___y_297_ = v___y_311_;
v___y_298_ = v___y_309_;
v___y_299_ = v___y_310_;
v___y_300_ = v___y_312_;
v___y_301_ = v___x_257_;
goto v___jp_296_;
}
}
v___jp_316_:
{
lean_object* v___x_318_; lean_object* v___f_319_; lean_object* v___x_320_; 
v___x_318_ = lean_box(0);
lean_inc(v___y_317_);
v___f_319_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed), 9, 2);
lean_closure_set(v___f_319_, 0, v___y_317_);
lean_closure_set(v___f_319_, 1, v___x_318_);
v___x_320_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_319_, v_a_248_, v_a_249_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_322_; lean_object* v_env_323_; lean_object* v___x_324_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc_n(v_a_321_, 2);
lean_dec_ref_known(v___x_320_, 1);
v___x_322_ = lean_st_ref_get(v_a_249_);
v_env_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc_ref(v_env_323_);
lean_dec(v___x_322_);
v___x_324_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_323_, v_a_321_);
if (lean_obj_tag(v___x_324_) == 1)
{
lean_object* v_val_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
lean_dec(v_docs_262_);
v_val_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_val_325_);
lean_dec_ref_known(v___x_324_, 1);
v___x_326_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8);
v___x_327_ = l_Lean_MessageData_ofConstName(v_a_321_, v___x_257_);
v___x_328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_326_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_328_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = l_Lean_MessageData_ofConstName(v_val_325_, v___x_257_);
v___x_332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___x_326_);
v___x_334_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v___y_317_, v___x_333_, v_a_248_, v_a_249_);
lean_dec(v___y_317_);
return v___x_334_;
}
else
{
lean_dec(v___x_324_);
v___y_309_ = v___y_317_;
v___y_310_ = v_a_321_;
v___y_311_ = v_a_248_;
v___y_312_ = v_a_249_;
goto v___jp_308_;
}
}
else
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
lean_dec(v___y_317_);
lean_dec(v_docs_262_);
v_a_335_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___x_320_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_320_);
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
v___jp_343_:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_unsigned_to_nat(2u);
v___x_345_ = l_Lean_Syntax_getArg(v_x_247_, v___x_344_);
lean_dec(v_x_247_);
if (v___x_257_ == 0)
{
lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_346_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14));
lean_inc(v___x_345_);
v___x_347_ = l_Lean_Syntax_isOfKind(v___x_345_, v___x_346_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; 
lean_dec(v___x_345_);
lean_dec(v_docs_262_);
v___x_348_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_349_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_348_, v_a_248_, v_a_249_);
return v___x_349_;
}
else
{
v___y_317_ = v___x_345_;
goto v___jp_316_;
}
}
else
{
v___y_317_ = v___x_345_;
goto v___jp_316_;
}
}
}
}
else
{
lean_object* v___x_354_; lean_object* v_cmd_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
lean_dec(v___x_256_);
v___x_354_ = lean_unsigned_to_nat(1u);
v_cmd_355_ = l_Lean_Syntax_getArg(v_x_247_, v___x_354_);
lean_dec(v_x_247_);
v___x_356_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18);
v___x_357_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_cmd_355_, v___x_356_, v_a_248_, v_a_249_);
lean_dec(v_cmd_355_);
return v___x_357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed(lean_object* v_x_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension(v_x_358_, v_a_359_, v_a_360_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(lean_object* v_msgData_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msgData_363_, v___y_365_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___boxed(lean_object* v_msgData_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(v_msgData_368_, v___y_369_, v___y_370_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(lean_object* v_00_u03b1_373_, lean_object* v_msg_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v_msg_374_, v___y_375_, v___y_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___boxed(lean_object* v_00_u03b1_379_, lean_object* v_msg_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(v_00_u03b1_379_, v_msg_380_, v___y_381_, v___y_382_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(lean_object* v_00_u03b1_385_, lean_object* v_ref_386_, lean_object* v_msg_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_ref_386_, v_msg_387_, v___y_388_, v___y_389_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___boxed(lean_object* v_00_u03b1_392_, lean_object* v_ref_393_, lean_object* v_msg_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(v_00_u03b1_392_, v_ref_393_, v_msg_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v_ref_393_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(lean_object* v_msgData_399_, lean_object* v_macroStack_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(v_msgData_399_, v_macroStack_400_, v___y_402_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___boxed(lean_object* v_msgData_405_, lean_object* v_macroStack_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(v_msgData_405_, v_macroStack_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1(){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_422_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_423_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4));
v___x_424_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_425_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed), 4, 0);
v___x_426_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_422_, v___x_423_, v___x_424_, v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3(){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_455_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_456_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6));
v___x_457_ = l_Lean_addBuiltinDeclarationRanges(v___x_455_, v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
return v_res_459_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0));
v___x_462_ = l_Lean_stringToMessageData(v___x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(lean_object* v_stx_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_val_475_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = l_Lean_Syntax_getArg(v_stx_464_, v___x_482_);
switch(lean_obj_tag(v___x_483_))
{
case 2:
{
lean_object* v_val_484_; 
lean_dec(v_stx_464_);
v_val_484_ = lean_ctor_get(v___x_483_, 1);
lean_inc_ref(v_val_484_);
lean_dec_ref_known(v___x_483_, 2);
v_val_475_ = v_val_484_;
goto v___jp_474_;
}
case 1:
{
lean_object* v_kind_485_; 
v_kind_485_ = lean_ctor_get(v___x_483_, 1);
lean_inc(v_kind_485_);
if (lean_obj_tag(v_kind_485_) == 1)
{
lean_object* v_pre_486_; 
v_pre_486_ = lean_ctor_get(v_kind_485_, 0);
lean_inc(v_pre_486_);
if (lean_obj_tag(v_pre_486_) == 1)
{
lean_object* v_pre_487_; 
v_pre_487_ = lean_ctor_get(v_pre_486_, 0);
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
if (lean_obj_tag(v_pre_489_) == 0)
{
lean_object* v_str_490_; lean_object* v_str_491_; lean_object* v_str_492_; lean_object* v_str_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v_str_490_ = lean_ctor_get(v_kind_485_, 1);
lean_inc_ref(v_str_490_);
lean_dec_ref_known(v_kind_485_, 2);
v_str_491_ = lean_ctor_get(v_pre_486_, 1);
lean_inc_ref(v_str_491_);
lean_dec_ref_known(v_pre_486_, 2);
v_str_492_ = lean_ctor_get(v_pre_487_, 1);
lean_inc_ref(v_str_492_);
lean_dec_ref_known(v_pre_487_, 2);
v_str_493_ = lean_ctor_get(v_pre_488_, 1);
lean_inc_ref(v_str_493_);
lean_dec_ref_known(v_pre_488_, 2);
v___x_494_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0));
v___x_495_ = lean_string_dec_eq(v_str_493_, v___x_494_);
lean_dec_ref(v_str_493_);
if (v___x_495_ == 0)
{
lean_dec_ref(v_str_492_);
lean_dec_ref(v_str_491_);
lean_dec_ref(v_str_490_);
lean_dec_ref_known(v___x_483_, 3);
goto v___jp_468_;
}
else
{
lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_496_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1));
v___x_497_ = lean_string_dec_eq(v_str_492_, v___x_496_);
lean_dec_ref(v_str_492_);
if (v___x_497_ == 0)
{
lean_dec_ref(v_str_491_);
lean_dec_ref(v_str_490_);
lean_dec_ref_known(v___x_483_, 3);
goto v___jp_468_;
}
else
{
lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_498_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2));
v___x_499_ = lean_string_dec_eq(v_str_491_, v___x_498_);
lean_dec_ref(v_str_491_);
if (v___x_499_ == 0)
{
lean_dec_ref(v_str_490_);
lean_dec_ref_known(v___x_483_, 3);
goto v___jp_468_;
}
else
{
lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2));
v___x_501_ = lean_string_dec_eq(v_str_490_, v___x_500_);
lean_dec_ref(v_str_490_);
if (v___x_501_ == 0)
{
lean_dec_ref_known(v___x_483_, 3);
goto v___jp_468_;
}
else
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_unsigned_to_nat(0u);
v___x_503_ = l_Lean_Syntax_getArg(v___x_483_, v___x_502_);
lean_dec_ref_known(v___x_483_, 3);
if (lean_obj_tag(v___x_503_) == 2)
{
lean_object* v_val_504_; 
lean_dec(v_stx_464_);
v_val_504_ = lean_ctor_get(v___x_503_, 1);
lean_inc_ref(v_val_504_);
lean_dec_ref_known(v___x_503_, 2);
v_val_475_ = v_val_504_;
goto v___jp_474_;
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec(v___x_503_);
v___x_505_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1);
lean_inc(v_stx_464_);
v___x_506_ = l_Lean_MessageData_ofSyntax(v_stx_464_);
v___x_507_ = l_Lean_indentD(v___x_506_);
v___x_508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_505_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_stx_464_, v___x_508_, v___y_465_, v___y_466_);
lean_dec(v_stx_464_);
return v___x_509_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_488_, 2);
lean_dec_ref_known(v_pre_487_, 2);
lean_dec_ref_known(v_pre_486_, 2);
lean_dec_ref_known(v_kind_485_, 2);
lean_dec_ref_known(v___x_483_, 3);
goto v___jp_468_;
}
}
else
{
lean_dec(v_pre_488_);
lean_dec_ref_known(v_pre_487_, 2);
lean_dec_ref_known(v_pre_486_, 2);
lean_dec_ref_known(v_kind_485_, 2);
lean_dec_ref_known(v___x_483_, 3);
goto v___jp_468_;
}
}
else
{
lean_dec_ref_known(v_pre_486_, 2);
lean_dec(v_pre_487_);
lean_dec_ref_known(v_kind_485_, 2);
lean_dec_ref_known(v___x_483_, 3);
goto v___jp_468_;
}
}
else
{
lean_dec(v_pre_486_);
lean_dec_ref_known(v_kind_485_, 2);
lean_dec_ref_known(v___x_483_, 3);
goto v___jp_468_;
}
}
else
{
lean_dec_ref_known(v___x_483_, 3);
lean_dec(v_kind_485_);
goto v___jp_468_;
}
}
default: 
{
lean_dec(v___x_483_);
goto v___jp_468_;
}
}
v___jp_468_:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_469_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1);
lean_inc(v_stx_464_);
v___x_470_ = l_Lean_MessageData_ofSyntax(v_stx_464_);
v___x_471_ = l_Lean_indentD(v___x_470_);
v___x_472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_469_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_stx_464_, v___x_472_, v___y_465_, v___y_466_);
lean_dec(v_stx_464_);
return v___x_473_;
}
v___jp_474_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_string_utf8_byte_size(v_val_475_);
v___x_478_ = lean_unsigned_to_nat(2u);
v___x_479_ = lean_nat_sub(v___x_477_, v___x_478_);
v___x_480_ = lean_string_utf8_extract(v_val_475_, v___x_476_, v___x_479_);
lean_dec(v___x_479_);
lean_dec_ref(v_val_475_);
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___boxed(lean_object* v_stx_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(v_stx_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
return v_res_514_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0));
v___x_517_ = l_Lean_stringToMessageData(v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(lean_object* v_x_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v_a_535_; lean_object* v_doc_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_603_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
lean_inc(v_x_527_);
v___x_604_ = l_Lean_Syntax_isOfKind(v_x_527_, v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec(v_x_527_);
v___x_605_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_606_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_605_, v_a_528_, v_a_529_);
return v___x_606_;
}
else
{
lean_object* v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = l_Lean_Syntax_getArg(v_x_527_, v___x_607_);
v___x_609_ = l_Lean_Syntax_isNone(v___x_608_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_608_);
v___x_611_ = l_Lean_Syntax_matchesNull(v___x_608_, v___x_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; lean_object* v___x_613_; 
lean_dec(v___x_608_);
lean_dec(v_x_527_);
v___x_612_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_613_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_612_, v_a_528_, v_a_529_);
return v___x_613_;
}
else
{
lean_object* v_doc_614_; 
v_doc_614_ = l_Lean_Syntax_getArg(v___x_608_, v___x_607_);
lean_dec(v___x_608_);
if (v___x_609_ == 0)
{
lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_617_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16));
lean_inc(v_doc_614_);
v___x_618_ = l_Lean_Syntax_isOfKind(v_doc_614_, v___x_617_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; lean_object* v___x_620_; 
lean_dec(v_doc_614_);
lean_dec(v_x_527_);
v___x_619_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_620_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_619_, v_a_528_, v_a_529_);
return v___x_620_;
}
else
{
goto v___jp_615_;
}
}
else
{
goto v___jp_615_;
}
v___jp_615_:
{
lean_object* v___x_616_; 
v___x_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_616_, 0, v_doc_614_);
v_doc_569_ = v___x_616_;
v___y_570_ = v_a_528_;
v___y_571_ = v_a_529_;
goto v___jp_568_;
}
}
}
else
{
lean_object* v___x_621_; 
lean_dec(v___x_608_);
v___x_621_ = lean_box(0);
v_doc_569_ = v___x_621_;
v___y_570_ = v_a_528_;
v___y_571_ = v_a_529_;
goto v___jp_568_;
}
}
v___jp_531_:
{
lean_object* v___x_536_; lean_object* v_env_537_; lean_object* v_messages_538_; lean_object* v_scopes_539_; lean_object* v_usedQuotCtxts_540_; lean_object* v_nextMacroScope_541_; lean_object* v_maxRecDepth_542_; lean_object* v_ngen_543_; lean_object* v_auxDeclNGen_544_; lean_object* v_infoState_545_; lean_object* v_traceState_546_; lean_object* v_snapshotTasks_547_; lean_object* v_prevLinterStates_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_567_; 
v___x_536_ = lean_st_ref_take(v___y_532_);
v_env_537_ = lean_ctor_get(v___x_536_, 0);
v_messages_538_ = lean_ctor_get(v___x_536_, 1);
v_scopes_539_ = lean_ctor_get(v___x_536_, 2);
v_usedQuotCtxts_540_ = lean_ctor_get(v___x_536_, 3);
v_nextMacroScope_541_ = lean_ctor_get(v___x_536_, 4);
v_maxRecDepth_542_ = lean_ctor_get(v___x_536_, 5);
v_ngen_543_ = lean_ctor_get(v___x_536_, 6);
v_auxDeclNGen_544_ = lean_ctor_get(v___x_536_, 7);
v_infoState_545_ = lean_ctor_get(v___x_536_, 8);
v_traceState_546_ = lean_ctor_get(v___x_536_, 9);
v_snapshotTasks_547_ = lean_ctor_get(v___x_536_, 10);
v_prevLinterStates_548_ = lean_ctor_get(v___x_536_, 11);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_567_ == 0)
{
v___x_550_ = v___x_536_;
v_isShared_551_ = v_isSharedCheck_567_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_prevLinterStates_548_);
lean_inc(v_snapshotTasks_547_);
lean_inc(v_traceState_546_);
lean_inc(v_infoState_545_);
lean_inc(v_auxDeclNGen_544_);
lean_inc(v_ngen_543_);
lean_inc(v_maxRecDepth_542_);
lean_inc(v_nextMacroScope_541_);
lean_inc(v_usedQuotCtxts_540_);
lean_inc(v_scopes_539_);
lean_inc(v_messages_538_);
lean_inc(v_env_537_);
lean_dec(v___x_536_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_567_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v_toEnvExtension_553_; lean_object* v_asyncMode_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_552_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_553_ = lean_ctor_get(v___x_552_, 0);
v_asyncMode_554_ = lean_ctor_get(v_toEnvExtension_553_, 2);
v___x_555_ = l_Lean_TSyntax_getId(v___y_534_);
lean_dec(v___y_534_);
v___x_556_ = l_Lean_TSyntax_getString(v___y_533_);
lean_dec(v___y_533_);
v___x_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
lean_ctor_set(v___x_557_, 1, v_a_535_);
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_555_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
v___x_559_ = lean_box(0);
v___x_560_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_552_, v_env_537_, v___x_558_, v_asyncMode_554_, v___x_559_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_560_);
v___x_562_ = v___x_550_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_messages_538_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v_scopes_539_);
lean_ctor_set(v_reuseFailAlloc_566_, 3, v_usedQuotCtxts_540_);
lean_ctor_set(v_reuseFailAlloc_566_, 4, v_nextMacroScope_541_);
lean_ctor_set(v_reuseFailAlloc_566_, 5, v_maxRecDepth_542_);
lean_ctor_set(v_reuseFailAlloc_566_, 6, v_ngen_543_);
lean_ctor_set(v_reuseFailAlloc_566_, 7, v_auxDeclNGen_544_);
lean_ctor_set(v_reuseFailAlloc_566_, 8, v_infoState_545_);
lean_ctor_set(v_reuseFailAlloc_566_, 9, v_traceState_546_);
lean_ctor_set(v_reuseFailAlloc_566_, 10, v_snapshotTasks_547_);
lean_ctor_set(v_reuseFailAlloc_566_, 11, v_prevLinterStates_548_);
v___x_562_ = v_reuseFailAlloc_566_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_563_ = lean_st_ref_put(v___y_532_, v___x_562_);
v___x_564_ = lean_box(0);
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
return v___x_565_;
}
}
}
v___jp_568_:
{
lean_object* v___x_572_; lean_object* v_tag_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_572_ = lean_unsigned_to_nat(2u);
v_tag_573_ = l_Lean_Syntax_getArg(v_x_527_, v___x_572_);
v___x_574_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14));
lean_inc(v_tag_573_);
v___x_575_ = l_Lean_Syntax_isOfKind(v_tag_573_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v_tag_573_);
lean_dec(v_doc_569_);
lean_dec(v_x_527_);
v___x_576_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_577_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_576_, v___y_570_, v___y_571_);
return v___x_577_;
}
else
{
lean_object* v___x_578_; lean_object* v_user_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_578_ = lean_unsigned_to_nat(3u);
v_user_579_ = l_Lean_Syntax_getArg(v_x_527_, v___x_578_);
lean_dec(v_x_527_);
v___x_580_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3));
lean_inc(v_user_579_);
v___x_581_ = l_Lean_Syntax_isOfKind(v_user_579_, v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec(v_user_579_);
lean_dec(v_tag_573_);
lean_dec(v_doc_569_);
v___x_582_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_583_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_582_, v___y_570_, v___y_571_);
return v___x_583_;
}
else
{
if (lean_obj_tag(v_doc_569_) == 0)
{
lean_object* v___x_584_; 
v___x_584_ = lean_box(0);
v___y_532_ = v___y_571_;
v___y_533_ = v_user_579_;
v___y_534_ = v_tag_573_;
v_a_535_ = v___x_584_;
goto v___jp_531_;
}
else
{
lean_object* v_val_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_602_; 
v_val_585_ = lean_ctor_get(v_doc_569_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v_doc_569_);
if (v_isSharedCheck_602_ == 0)
{
v___x_587_ = v_doc_569_;
v_isShared_588_ = v_isSharedCheck_602_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_val_585_);
lean_dec(v_doc_569_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_602_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(v_val_585_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_592_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_590_);
lean_dec_ref_known(v___x_589_, 1);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v_a_590_);
v___x_592_ = v___x_587_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
v___y_532_ = v___y_571_;
v___y_533_ = v_user_579_;
v___y_534_ = v_tag_573_;
v_a_535_ = v___x_592_;
goto v___jp_531_;
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_del_object(v___x_587_);
lean_dec(v_user_579_);
lean_dec(v_tag_573_);
v_a_594_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_589_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_589_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed(lean_object* v_x_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(v_x_622_, v_a_623_, v_a_624_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1(){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_635_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_636_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
v___x_637_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_638_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed), 4, 0);
v___x_639_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_635_, v___x_636_, v___x_637_, v___x_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3(){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_668_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_669_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6));
v___x_670_ = l_Lean_addBuiltinDeclarationRanges(v___x_668_, v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(lean_object* v___x_673_, lean_object* v_x_674_){
_start:
{
if (lean_obj_tag(v_x_674_) == 0)
{
lean_object* v___x_675_; 
v___x_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_673_);
return v___x_675_;
}
else
{
lean_dec_ref(v___x_673_);
lean_inc_ref(v_x_674_);
return v_x_674_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_676_, lean_object* v_x_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_676_, v_x_677_);
lean_dec(v_x_677_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(lean_object* v___x_679_, lean_object* v_k_680_, lean_object* v_t_681_){
_start:
{
if (lean_obj_tag(v_t_681_) == 0)
{
lean_object* v_size_682_; lean_object* v_k_683_; lean_object* v_v_684_; lean_object* v_l_685_; lean_object* v_r_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_1012_; 
v_size_682_ = lean_ctor_get(v_t_681_, 0);
v_k_683_ = lean_ctor_get(v_t_681_, 1);
v_v_684_ = lean_ctor_get(v_t_681_, 2);
v_l_685_ = lean_ctor_get(v_t_681_, 3);
v_r_686_ = lean_ctor_get(v_t_681_, 4);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_t_681_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_688_ = v_t_681_;
v_isShared_689_ = v_isSharedCheck_1012_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_r_686_);
lean_inc(v_l_685_);
lean_inc(v_v_684_);
lean_inc(v_k_683_);
lean_inc(v_size_682_);
lean_dec(v_t_681_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_1012_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
uint8_t v___x_690_; 
v___x_690_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_680_, v_k_683_);
switch(v___x_690_)
{
case 0:
{
lean_object* v_impl_691_; lean_object* v___x_692_; 
lean_del_object(v___x_688_);
lean_dec(v_size_682_);
v_impl_691_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_679_, v_k_680_, v_l_685_);
v___x_692_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_683_, v_v_684_, v_impl_691_, v_r_686_);
return v___x_692_;
}
case 1:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
lean_dec(v_k_683_);
v___x_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_693_, 0, v_v_684_);
v___x_694_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_679_, v___x_693_);
lean_dec_ref_known(v___x_693_, 1);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_del_object(v___x_688_);
lean_dec(v_size_682_);
lean_dec(v_k_680_);
if (lean_obj_tag(v_l_685_) == 0)
{
if (lean_obj_tag(v_r_686_) == 0)
{
lean_object* v_size_695_; lean_object* v_k_696_; lean_object* v_v_697_; lean_object* v_l_698_; lean_object* v_r_699_; lean_object* v_size_700_; lean_object* v_k_701_; lean_object* v_v_702_; lean_object* v_l_703_; lean_object* v_r_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v_size_695_ = lean_ctor_get(v_l_685_, 0);
v_k_696_ = lean_ctor_get(v_l_685_, 1);
v_v_697_ = lean_ctor_get(v_l_685_, 2);
v_l_698_ = lean_ctor_get(v_l_685_, 3);
v_r_699_ = lean_ctor_get(v_l_685_, 4);
lean_inc(v_r_699_);
v_size_700_ = lean_ctor_get(v_r_686_, 0);
v_k_701_ = lean_ctor_get(v_r_686_, 1);
v_v_702_ = lean_ctor_get(v_r_686_, 2);
v_l_703_ = lean_ctor_get(v_r_686_, 3);
lean_inc(v_l_703_);
v_r_704_ = lean_ctor_get(v_r_686_, 4);
v___x_705_ = lean_unsigned_to_nat(1u);
v___x_706_ = lean_nat_dec_lt(v_size_695_, v_size_700_);
if (v___x_706_ == 0)
{
lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_842_; 
lean_inc(v_l_698_);
lean_inc(v_v_697_);
lean_inc(v_k_696_);
v_isSharedCheck_842_ = !lean_is_exclusive(v_l_685_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; lean_object* v_unused_844_; lean_object* v_unused_845_; lean_object* v_unused_846_; lean_object* v_unused_847_; 
v_unused_843_ = lean_ctor_get(v_l_685_, 4);
lean_dec(v_unused_843_);
v_unused_844_ = lean_ctor_get(v_l_685_, 3);
lean_dec(v_unused_844_);
v_unused_845_ = lean_ctor_get(v_l_685_, 2);
lean_dec(v_unused_845_);
v_unused_846_ = lean_ctor_get(v_l_685_, 1);
lean_dec(v_unused_846_);
v_unused_847_ = lean_ctor_get(v_l_685_, 0);
lean_dec(v_unused_847_);
v___x_708_ = v_l_685_;
v_isShared_709_ = v_isSharedCheck_842_;
goto v_resetjp_707_;
}
else
{
lean_dec(v_l_685_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_842_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v_tree_711_; 
v___x_710_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_696_, v_v_697_, v_l_698_, v_r_699_);
v_tree_711_ = lean_ctor_get(v___x_710_, 2);
lean_inc(v_tree_711_);
if (lean_obj_tag(v_tree_711_) == 0)
{
lean_object* v_k_712_; lean_object* v_v_713_; lean_object* v_size_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v_k_712_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_k_712_);
v_v_713_ = lean_ctor_get(v___x_710_, 1);
lean_inc(v_v_713_);
lean_dec_ref(v___x_710_);
v_size_714_ = lean_ctor_get(v_tree_711_, 0);
v___x_715_ = lean_unsigned_to_nat(3u);
v___x_716_ = lean_nat_mul(v___x_715_, v_size_714_);
v___x_717_ = lean_nat_dec_lt(v___x_716_, v_size_700_);
lean_dec(v___x_716_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
lean_dec(v_l_703_);
v___x_718_ = lean_nat_add(v___x_705_, v_size_714_);
v___x_719_ = lean_nat_add(v___x_718_, v_size_700_);
lean_dec(v___x_718_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 4, v_r_686_);
lean_ctor_set(v___x_708_, 3, v_tree_711_);
lean_ctor_set(v___x_708_, 2, v_v_713_);
lean_ctor_set(v___x_708_, 1, v_k_712_);
lean_ctor_set(v___x_708_, 0, v___x_719_);
v___x_721_ = v___x_708_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_k_712_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v_v_713_);
lean_ctor_set(v_reuseFailAlloc_722_, 3, v_tree_711_);
lean_ctor_set(v_reuseFailAlloc_722_, 4, v_r_686_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
else
{
lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_777_; 
lean_inc(v_r_704_);
lean_inc(v_v_702_);
lean_inc(v_k_701_);
lean_inc(v_size_700_);
v_isSharedCheck_777_ = !lean_is_exclusive(v_r_686_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; lean_object* v_unused_779_; lean_object* v_unused_780_; lean_object* v_unused_781_; lean_object* v_unused_782_; 
v_unused_778_ = lean_ctor_get(v_r_686_, 4);
lean_dec(v_unused_778_);
v_unused_779_ = lean_ctor_get(v_r_686_, 3);
lean_dec(v_unused_779_);
v_unused_780_ = lean_ctor_get(v_r_686_, 2);
lean_dec(v_unused_780_);
v_unused_781_ = lean_ctor_get(v_r_686_, 1);
lean_dec(v_unused_781_);
v_unused_782_ = lean_ctor_get(v_r_686_, 0);
lean_dec(v_unused_782_);
v___x_724_ = v_r_686_;
v_isShared_725_ = v_isSharedCheck_777_;
goto v_resetjp_723_;
}
else
{
lean_dec(v_r_686_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_777_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v_size_726_; lean_object* v_k_727_; lean_object* v_v_728_; lean_object* v_l_729_; lean_object* v_r_730_; lean_object* v_size_731_; lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v_size_726_ = lean_ctor_get(v_l_703_, 0);
v_k_727_ = lean_ctor_get(v_l_703_, 1);
v_v_728_ = lean_ctor_get(v_l_703_, 2);
v_l_729_ = lean_ctor_get(v_l_703_, 3);
v_r_730_ = lean_ctor_get(v_l_703_, 4);
v_size_731_ = lean_ctor_get(v_r_704_, 0);
v___x_732_ = lean_unsigned_to_nat(2u);
v___x_733_ = lean_nat_mul(v___x_732_, v_size_731_);
v___x_734_ = lean_nat_dec_lt(v_size_726_, v___x_733_);
lean_dec(v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_762_; 
lean_inc(v_r_730_);
lean_inc(v_l_729_);
lean_inc(v_v_728_);
lean_inc(v_k_727_);
v_isSharedCheck_762_ = !lean_is_exclusive(v_l_703_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; lean_object* v_unused_764_; lean_object* v_unused_765_; lean_object* v_unused_766_; lean_object* v_unused_767_; 
v_unused_763_ = lean_ctor_get(v_l_703_, 4);
lean_dec(v_unused_763_);
v_unused_764_ = lean_ctor_get(v_l_703_, 3);
lean_dec(v_unused_764_);
v_unused_765_ = lean_ctor_get(v_l_703_, 2);
lean_dec(v_unused_765_);
v_unused_766_ = lean_ctor_get(v_l_703_, 1);
lean_dec(v_unused_766_);
v_unused_767_ = lean_ctor_get(v_l_703_, 0);
lean_dec(v_unused_767_);
v___x_736_ = v_l_703_;
v_isShared_737_ = v_isSharedCheck_762_;
goto v_resetjp_735_;
}
else
{
lean_dec(v_l_703_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_762_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_752_; 
v___x_738_ = lean_nat_add(v___x_705_, v_size_714_);
v___x_739_ = lean_nat_add(v___x_738_, v_size_700_);
lean_dec(v_size_700_);
if (lean_obj_tag(v_l_729_) == 0)
{
lean_object* v_size_760_; 
v_size_760_ = lean_ctor_get(v_l_729_, 0);
lean_inc(v_size_760_);
v___y_752_ = v_size_760_;
goto v___jp_751_;
}
else
{
lean_object* v___x_761_; 
v___x_761_ = lean_unsigned_to_nat(0u);
v___y_752_ = v___x_761_;
goto v___jp_751_;
}
v___jp_740_:
{
lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_744_ = lean_nat_add(v___y_741_, v___y_743_);
lean_dec(v___y_743_);
lean_dec(v___y_741_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 4, v_r_704_);
lean_ctor_set(v___x_736_, 3, v_r_730_);
lean_ctor_set(v___x_736_, 2, v_v_702_);
lean_ctor_set(v___x_736_, 1, v_k_701_);
lean_ctor_set(v___x_736_, 0, v___x_744_);
v___x_746_ = v___x_736_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_k_701_);
lean_ctor_set(v_reuseFailAlloc_750_, 2, v_v_702_);
lean_ctor_set(v_reuseFailAlloc_750_, 3, v_r_730_);
lean_ctor_set(v_reuseFailAlloc_750_, 4, v_r_704_);
v___x_746_ = v_reuseFailAlloc_750_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_748_; 
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 4, v___x_746_);
lean_ctor_set(v___x_724_, 3, v___y_742_);
lean_ctor_set(v___x_724_, 2, v_v_728_);
lean_ctor_set(v___x_724_, 1, v_k_727_);
lean_ctor_set(v___x_724_, 0, v___x_739_);
v___x_748_ = v___x_724_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_k_727_);
lean_ctor_set(v_reuseFailAlloc_749_, 2, v_v_728_);
lean_ctor_set(v_reuseFailAlloc_749_, 3, v___y_742_);
lean_ctor_set(v_reuseFailAlloc_749_, 4, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
v___jp_751_:
{
lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_753_ = lean_nat_add(v___x_738_, v___y_752_);
lean_dec(v___y_752_);
lean_dec(v___x_738_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 4, v_l_729_);
lean_ctor_set(v___x_708_, 3, v_tree_711_);
lean_ctor_set(v___x_708_, 2, v_v_713_);
lean_ctor_set(v___x_708_, 1, v_k_712_);
lean_ctor_set(v___x_708_, 0, v___x_753_);
v___x_755_ = v___x_708_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_k_712_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v_v_713_);
lean_ctor_set(v_reuseFailAlloc_759_, 3, v_tree_711_);
lean_ctor_set(v_reuseFailAlloc_759_, 4, v_l_729_);
v___x_755_ = v_reuseFailAlloc_759_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_756_; 
v___x_756_ = lean_nat_add(v___x_705_, v_size_731_);
if (lean_obj_tag(v_r_730_) == 0)
{
lean_object* v_size_757_; 
v_size_757_ = lean_ctor_get(v_r_730_, 0);
lean_inc(v_size_757_);
v___y_741_ = v___x_756_;
v___y_742_ = v___x_755_;
v___y_743_ = v_size_757_;
goto v___jp_740_;
}
else
{
lean_object* v___x_758_; 
v___x_758_ = lean_unsigned_to_nat(0u);
v___y_741_ = v___x_756_;
v___y_742_ = v___x_755_;
v___y_743_ = v___x_758_;
goto v___jp_740_;
}
}
}
}
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_768_ = lean_nat_add(v___x_705_, v_size_714_);
v___x_769_ = lean_nat_add(v___x_768_, v_size_700_);
lean_dec(v_size_700_);
v___x_770_ = lean_nat_add(v___x_768_, v_size_726_);
lean_dec(v___x_768_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 4, v_l_703_);
lean_ctor_set(v___x_724_, 3, v_tree_711_);
lean_ctor_set(v___x_724_, 2, v_v_713_);
lean_ctor_set(v___x_724_, 1, v_k_712_);
lean_ctor_set(v___x_724_, 0, v___x_770_);
v___x_772_ = v___x_724_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_k_712_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v_v_713_);
lean_ctor_set(v_reuseFailAlloc_776_, 3, v_tree_711_);
lean_ctor_set(v_reuseFailAlloc_776_, 4, v_l_703_);
v___x_772_ = v_reuseFailAlloc_776_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_774_; 
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 4, v_r_704_);
lean_ctor_set(v___x_708_, 3, v___x_772_);
lean_ctor_set(v___x_708_, 2, v_v_702_);
lean_ctor_set(v___x_708_, 1, v_k_701_);
lean_ctor_set(v___x_708_, 0, v___x_769_);
v___x_774_ = v___x_708_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_k_701_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v_v_702_);
lean_ctor_set(v_reuseFailAlloc_775_, 3, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_775_, 4, v_r_704_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
}
else
{
lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_836_; 
lean_inc(v_r_704_);
lean_inc(v_v_702_);
lean_inc(v_k_701_);
lean_inc(v_size_700_);
v_isSharedCheck_836_ = !lean_is_exclusive(v_r_686_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; lean_object* v_unused_838_; lean_object* v_unused_839_; lean_object* v_unused_840_; lean_object* v_unused_841_; 
v_unused_837_ = lean_ctor_get(v_r_686_, 4);
lean_dec(v_unused_837_);
v_unused_838_ = lean_ctor_get(v_r_686_, 3);
lean_dec(v_unused_838_);
v_unused_839_ = lean_ctor_get(v_r_686_, 2);
lean_dec(v_unused_839_);
v_unused_840_ = lean_ctor_get(v_r_686_, 1);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v_r_686_, 0);
lean_dec(v_unused_841_);
v___x_784_ = v_r_686_;
v_isShared_785_ = v_isSharedCheck_836_;
goto v_resetjp_783_;
}
else
{
lean_dec(v_r_686_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_836_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
if (lean_obj_tag(v_l_703_) == 0)
{
if (lean_obj_tag(v_r_704_) == 0)
{
lean_object* v_k_786_; lean_object* v_v_787_; lean_object* v_size_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v_k_786_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_k_786_);
v_v_787_ = lean_ctor_get(v___x_710_, 1);
lean_inc(v_v_787_);
lean_dec_ref(v___x_710_);
v_size_788_ = lean_ctor_get(v_l_703_, 0);
v___x_789_ = lean_nat_add(v___x_705_, v_size_700_);
lean_dec(v_size_700_);
v___x_790_ = lean_nat_add(v___x_705_, v_size_788_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 4, v_l_703_);
lean_ctor_set(v___x_784_, 3, v_tree_711_);
lean_ctor_set(v___x_784_, 2, v_v_787_);
lean_ctor_set(v___x_784_, 1, v_k_786_);
lean_ctor_set(v___x_784_, 0, v___x_790_);
v___x_792_ = v___x_784_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_k_786_);
lean_ctor_set(v_reuseFailAlloc_796_, 2, v_v_787_);
lean_ctor_set(v_reuseFailAlloc_796_, 3, v_tree_711_);
lean_ctor_set(v_reuseFailAlloc_796_, 4, v_l_703_);
v___x_792_ = v_reuseFailAlloc_796_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_794_; 
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 4, v_r_704_);
lean_ctor_set(v___x_708_, 3, v___x_792_);
lean_ctor_set(v___x_708_, 2, v_v_702_);
lean_ctor_set(v___x_708_, 1, v_k_701_);
lean_ctor_set(v___x_708_, 0, v___x_789_);
v___x_794_ = v___x_708_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_k_701_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v_v_702_);
lean_ctor_set(v_reuseFailAlloc_795_, 3, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_795_, 4, v_r_704_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
else
{
lean_object* v_k_797_; lean_object* v_v_798_; lean_object* v_k_799_; lean_object* v_v_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_814_; 
lean_dec(v_size_700_);
v_k_797_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_k_797_);
v_v_798_ = lean_ctor_get(v___x_710_, 1);
lean_inc(v_v_798_);
lean_dec_ref(v___x_710_);
v_k_799_ = lean_ctor_get(v_l_703_, 1);
v_v_800_ = lean_ctor_get(v_l_703_, 2);
v_isSharedCheck_814_ = !lean_is_exclusive(v_l_703_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; lean_object* v_unused_816_; lean_object* v_unused_817_; 
v_unused_815_ = lean_ctor_get(v_l_703_, 4);
lean_dec(v_unused_815_);
v_unused_816_ = lean_ctor_get(v_l_703_, 3);
lean_dec(v_unused_816_);
v_unused_817_ = lean_ctor_get(v_l_703_, 0);
lean_dec(v_unused_817_);
v___x_802_ = v_l_703_;
v_isShared_803_ = v_isSharedCheck_814_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_v_800_);
lean_inc(v_k_799_);
lean_dec(v_l_703_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_814_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_804_ = lean_unsigned_to_nat(3u);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 4, v_r_704_);
lean_ctor_set(v___x_802_, 3, v_r_704_);
lean_ctor_set(v___x_802_, 2, v_v_798_);
lean_ctor_set(v___x_802_, 1, v_k_797_);
lean_ctor_set(v___x_802_, 0, v___x_705_);
v___x_806_ = v___x_802_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_k_797_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v_v_798_);
lean_ctor_set(v_reuseFailAlloc_813_, 3, v_r_704_);
lean_ctor_set(v_reuseFailAlloc_813_, 4, v_r_704_);
v___x_806_ = v_reuseFailAlloc_813_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_808_; 
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 3, v_r_704_);
lean_ctor_set(v___x_784_, 0, v___x_705_);
v___x_808_ = v___x_784_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_k_701_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v_v_702_);
lean_ctor_set(v_reuseFailAlloc_812_, 3, v_r_704_);
lean_ctor_set(v_reuseFailAlloc_812_, 4, v_r_704_);
v___x_808_ = v_reuseFailAlloc_812_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_810_; 
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 4, v___x_808_);
lean_ctor_set(v___x_708_, 3, v___x_806_);
lean_ctor_set(v___x_708_, 2, v_v_800_);
lean_ctor_set(v___x_708_, 1, v_k_799_);
lean_ctor_set(v___x_708_, 0, v___x_804_);
v___x_810_ = v___x_708_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_804_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_k_799_);
lean_ctor_set(v_reuseFailAlloc_811_, 2, v_v_800_);
lean_ctor_set(v_reuseFailAlloc_811_, 3, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_811_, 4, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_704_) == 0)
{
lean_object* v_k_818_; lean_object* v_v_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
lean_dec(v_size_700_);
v_k_818_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_k_818_);
v_v_819_ = lean_ctor_get(v___x_710_, 1);
lean_inc(v_v_819_);
lean_dec_ref(v___x_710_);
v___x_820_ = lean_unsigned_to_nat(3u);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 4, v_l_703_);
lean_ctor_set(v___x_784_, 2, v_v_819_);
lean_ctor_set(v___x_784_, 1, v_k_818_);
lean_ctor_set(v___x_784_, 0, v___x_705_);
v___x_822_ = v___x_784_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_k_818_);
lean_ctor_set(v_reuseFailAlloc_826_, 2, v_v_819_);
lean_ctor_set(v_reuseFailAlloc_826_, 3, v_l_703_);
lean_ctor_set(v_reuseFailAlloc_826_, 4, v_l_703_);
v___x_822_ = v_reuseFailAlloc_826_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_824_; 
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 4, v_r_704_);
lean_ctor_set(v___x_708_, 3, v___x_822_);
lean_ctor_set(v___x_708_, 2, v_v_702_);
lean_ctor_set(v___x_708_, 1, v_k_701_);
lean_ctor_set(v___x_708_, 0, v___x_820_);
v___x_824_ = v___x_708_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_820_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_k_701_);
lean_ctor_set(v_reuseFailAlloc_825_, 2, v_v_702_);
lean_ctor_set(v_reuseFailAlloc_825_, 3, v___x_822_);
lean_ctor_set(v_reuseFailAlloc_825_, 4, v_r_704_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
else
{
lean_object* v_k_827_; lean_object* v_v_828_; lean_object* v___x_830_; 
v_k_827_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_k_827_);
v_v_828_ = lean_ctor_get(v___x_710_, 1);
lean_inc(v_v_828_);
lean_dec_ref(v___x_710_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 3, v_r_704_);
v___x_830_ = v___x_784_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_size_700_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_k_701_);
lean_ctor_set(v_reuseFailAlloc_835_, 2, v_v_702_);
lean_ctor_set(v_reuseFailAlloc_835_, 3, v_r_704_);
lean_ctor_set(v_reuseFailAlloc_835_, 4, v_r_704_);
v___x_830_ = v_reuseFailAlloc_835_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_831_ = lean_unsigned_to_nat(2u);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 4, v___x_830_);
lean_ctor_set(v___x_708_, 3, v_r_704_);
lean_ctor_set(v___x_708_, 2, v_v_828_);
lean_ctor_set(v___x_708_, 1, v_k_827_);
lean_ctor_set(v___x_708_, 0, v___x_831_);
v___x_833_ = v___x_708_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_831_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_k_827_);
lean_ctor_set(v_reuseFailAlloc_834_, 2, v_v_828_);
lean_ctor_set(v_reuseFailAlloc_834_, 3, v_r_704_);
lean_ctor_set(v_reuseFailAlloc_834_, 4, v___x_830_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
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
lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_1000_; 
lean_inc(v_r_704_);
lean_inc(v_v_702_);
lean_inc(v_k_701_);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_r_686_);
if (v_isSharedCheck_1000_ == 0)
{
lean_object* v_unused_1001_; lean_object* v_unused_1002_; lean_object* v_unused_1003_; lean_object* v_unused_1004_; lean_object* v_unused_1005_; 
v_unused_1001_ = lean_ctor_get(v_r_686_, 4);
lean_dec(v_unused_1001_);
v_unused_1002_ = lean_ctor_get(v_r_686_, 3);
lean_dec(v_unused_1002_);
v_unused_1003_ = lean_ctor_get(v_r_686_, 2);
lean_dec(v_unused_1003_);
v_unused_1004_ = lean_ctor_get(v_r_686_, 1);
lean_dec(v_unused_1004_);
v_unused_1005_ = lean_ctor_get(v_r_686_, 0);
lean_dec(v_unused_1005_);
v___x_849_ = v_r_686_;
v_isShared_850_ = v_isSharedCheck_1000_;
goto v_resetjp_848_;
}
else
{
lean_dec(v_r_686_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_1000_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v_tree_852_; 
v___x_851_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_701_, v_v_702_, v_l_703_, v_r_704_);
v_tree_852_ = lean_ctor_get(v___x_851_, 2);
lean_inc(v_tree_852_);
if (lean_obj_tag(v_tree_852_) == 0)
{
lean_object* v_k_853_; lean_object* v_v_854_; lean_object* v_size_855_; lean_object* v___x_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v_k_853_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_k_853_);
v_v_854_ = lean_ctor_get(v___x_851_, 1);
lean_inc(v_v_854_);
lean_dec_ref(v___x_851_);
v_size_855_ = lean_ctor_get(v_tree_852_, 0);
v___x_856_ = lean_unsigned_to_nat(3u);
v___x_857_ = lean_nat_mul(v___x_856_, v_size_855_);
v___x_858_ = lean_nat_dec_lt(v___x_857_, v_size_695_);
lean_dec(v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_862_; 
lean_dec(v_r_699_);
v___x_859_ = lean_nat_add(v___x_705_, v_size_695_);
v___x_860_ = lean_nat_add(v___x_859_, v_size_855_);
lean_dec(v___x_859_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 4, v_tree_852_);
lean_ctor_set(v___x_849_, 3, v_l_685_);
lean_ctor_set(v___x_849_, 2, v_v_854_);
lean_ctor_set(v___x_849_, 1, v_k_853_);
lean_ctor_set(v___x_849_, 0, v___x_860_);
v___x_862_ = v___x_849_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_k_853_);
lean_ctor_set(v_reuseFailAlloc_863_, 2, v_v_854_);
lean_ctor_set(v_reuseFailAlloc_863_, 3, v_l_685_);
lean_ctor_set(v_reuseFailAlloc_863_, 4, v_tree_852_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
else
{
lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_929_; 
lean_inc(v_l_698_);
lean_inc(v_v_697_);
lean_inc(v_k_696_);
lean_inc(v_size_695_);
v_isSharedCheck_929_ = !lean_is_exclusive(v_l_685_);
if (v_isSharedCheck_929_ == 0)
{
lean_object* v_unused_930_; lean_object* v_unused_931_; lean_object* v_unused_932_; lean_object* v_unused_933_; lean_object* v_unused_934_; 
v_unused_930_ = lean_ctor_get(v_l_685_, 4);
lean_dec(v_unused_930_);
v_unused_931_ = lean_ctor_get(v_l_685_, 3);
lean_dec(v_unused_931_);
v_unused_932_ = lean_ctor_get(v_l_685_, 2);
lean_dec(v_unused_932_);
v_unused_933_ = lean_ctor_get(v_l_685_, 1);
lean_dec(v_unused_933_);
v_unused_934_ = lean_ctor_get(v_l_685_, 0);
lean_dec(v_unused_934_);
v___x_865_ = v_l_685_;
v_isShared_866_ = v_isSharedCheck_929_;
goto v_resetjp_864_;
}
else
{
lean_dec(v_l_685_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_929_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v_size_867_; lean_object* v_size_868_; lean_object* v_k_869_; lean_object* v_v_870_; lean_object* v_l_871_; lean_object* v_r_872_; lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v_size_867_ = lean_ctor_get(v_l_698_, 0);
v_size_868_ = lean_ctor_get(v_r_699_, 0);
v_k_869_ = lean_ctor_get(v_r_699_, 1);
v_v_870_ = lean_ctor_get(v_r_699_, 2);
v_l_871_ = lean_ctor_get(v_r_699_, 3);
v_r_872_ = lean_ctor_get(v_r_699_, 4);
v___x_873_ = lean_unsigned_to_nat(2u);
v___x_874_ = lean_nat_mul(v___x_873_, v_size_867_);
v___x_875_ = lean_nat_dec_lt(v_size_868_, v___x_874_);
lean_dec(v___x_874_);
if (v___x_875_ == 0)
{
lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_913_; 
lean_inc(v_r_872_);
lean_inc(v_l_871_);
lean_inc(v_v_870_);
lean_inc(v_k_869_);
lean_del_object(v___x_865_);
v_isSharedCheck_913_ = !lean_is_exclusive(v_r_699_);
if (v_isSharedCheck_913_ == 0)
{
lean_object* v_unused_914_; lean_object* v_unused_915_; lean_object* v_unused_916_; lean_object* v_unused_917_; lean_object* v_unused_918_; 
v_unused_914_ = lean_ctor_get(v_r_699_, 4);
lean_dec(v_unused_914_);
v_unused_915_ = lean_ctor_get(v_r_699_, 3);
lean_dec(v_unused_915_);
v_unused_916_ = lean_ctor_get(v_r_699_, 2);
lean_dec(v_unused_916_);
v_unused_917_ = lean_ctor_get(v_r_699_, 1);
lean_dec(v_unused_917_);
v_unused_918_ = lean_ctor_get(v_r_699_, 0);
lean_dec(v_unused_918_);
v___x_877_ = v_r_699_;
v_isShared_878_ = v_isSharedCheck_913_;
goto v_resetjp_876_;
}
else
{
lean_dec(v_r_699_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_913_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___x_901_; lean_object* v___y_903_; 
v___x_879_ = lean_nat_add(v___x_705_, v_size_695_);
lean_dec(v_size_695_);
v___x_880_ = lean_nat_add(v___x_879_, v_size_855_);
lean_dec(v___x_879_);
v___x_901_ = lean_nat_add(v___x_705_, v_size_867_);
if (lean_obj_tag(v_l_871_) == 0)
{
lean_object* v_size_911_; 
v_size_911_ = lean_ctor_get(v_l_871_, 0);
lean_inc(v_size_911_);
v___y_903_ = v_size_911_;
goto v___jp_902_;
}
else
{
lean_object* v___x_912_; 
v___x_912_ = lean_unsigned_to_nat(0u);
v___y_903_ = v___x_912_;
goto v___jp_902_;
}
v___jp_881_:
{
lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_885_ = lean_nat_add(v___y_883_, v___y_884_);
lean_dec(v___y_884_);
lean_dec(v___y_883_);
lean_inc_ref(v_tree_852_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 4, v_tree_852_);
lean_ctor_set(v___x_877_, 3, v_r_872_);
lean_ctor_set(v___x_877_, 2, v_v_854_);
lean_ctor_set(v___x_877_, 1, v_k_853_);
lean_ctor_set(v___x_877_, 0, v___x_885_);
v___x_887_ = v___x_877_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_885_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_k_853_);
lean_ctor_set(v_reuseFailAlloc_900_, 2, v_v_854_);
lean_ctor_set(v_reuseFailAlloc_900_, 3, v_r_872_);
lean_ctor_set(v_reuseFailAlloc_900_, 4, v_tree_852_);
v___x_887_ = v_reuseFailAlloc_900_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
v_isSharedCheck_894_ = !lean_is_exclusive(v_tree_852_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; lean_object* v_unused_896_; lean_object* v_unused_897_; lean_object* v_unused_898_; lean_object* v_unused_899_; 
v_unused_895_ = lean_ctor_get(v_tree_852_, 4);
lean_dec(v_unused_895_);
v_unused_896_ = lean_ctor_get(v_tree_852_, 3);
lean_dec(v_unused_896_);
v_unused_897_ = lean_ctor_get(v_tree_852_, 2);
lean_dec(v_unused_897_);
v_unused_898_ = lean_ctor_get(v_tree_852_, 1);
lean_dec(v_unused_898_);
v_unused_899_ = lean_ctor_get(v_tree_852_, 0);
lean_dec(v_unused_899_);
v___x_889_ = v_tree_852_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_dec(v_tree_852_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 4, v___x_887_);
lean_ctor_set(v___x_889_, 3, v___y_882_);
lean_ctor_set(v___x_889_, 2, v_v_870_);
lean_ctor_set(v___x_889_, 1, v_k_869_);
lean_ctor_set(v___x_889_, 0, v___x_880_);
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_k_869_);
lean_ctor_set(v_reuseFailAlloc_893_, 2, v_v_870_);
lean_ctor_set(v_reuseFailAlloc_893_, 3, v___y_882_);
lean_ctor_set(v_reuseFailAlloc_893_, 4, v___x_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
v___jp_902_:
{
lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_904_ = lean_nat_add(v___x_901_, v___y_903_);
lean_dec(v___y_903_);
lean_dec(v___x_901_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 4, v_l_871_);
lean_ctor_set(v___x_849_, 3, v_l_698_);
lean_ctor_set(v___x_849_, 2, v_v_697_);
lean_ctor_set(v___x_849_, 1, v_k_696_);
lean_ctor_set(v___x_849_, 0, v___x_904_);
v___x_906_ = v___x_849_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_910_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_910_, 3, v_l_698_);
lean_ctor_set(v_reuseFailAlloc_910_, 4, v_l_871_);
v___x_906_ = v_reuseFailAlloc_910_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_907_; 
v___x_907_ = lean_nat_add(v___x_705_, v_size_855_);
if (lean_obj_tag(v_r_872_) == 0)
{
lean_object* v_size_908_; 
v_size_908_ = lean_ctor_get(v_r_872_, 0);
lean_inc(v_size_908_);
v___y_882_ = v___x_906_;
v___y_883_ = v___x_907_;
v___y_884_ = v_size_908_;
goto v___jp_881_;
}
else
{
lean_object* v___x_909_; 
v___x_909_ = lean_unsigned_to_nat(0u);
v___y_882_ = v___x_906_;
v___y_883_ = v___x_907_;
v___y_884_ = v___x_909_;
goto v___jp_881_;
}
}
}
}
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_919_ = lean_nat_add(v___x_705_, v_size_695_);
lean_dec(v_size_695_);
v___x_920_ = lean_nat_add(v___x_919_, v_size_855_);
lean_dec(v___x_919_);
v___x_921_ = lean_nat_add(v___x_705_, v_size_855_);
v___x_922_ = lean_nat_add(v___x_921_, v_size_868_);
lean_dec(v___x_921_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 4, v_tree_852_);
lean_ctor_set(v___x_849_, 3, v_r_699_);
lean_ctor_set(v___x_849_, 2, v_v_854_);
lean_ctor_set(v___x_849_, 1, v_k_853_);
lean_ctor_set(v___x_849_, 0, v___x_922_);
v___x_924_ = v___x_849_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_922_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v_k_853_);
lean_ctor_set(v_reuseFailAlloc_928_, 2, v_v_854_);
lean_ctor_set(v_reuseFailAlloc_928_, 3, v_r_699_);
lean_ctor_set(v_reuseFailAlloc_928_, 4, v_tree_852_);
v___x_924_ = v_reuseFailAlloc_928_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
lean_object* v___x_926_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 4, v___x_924_);
lean_ctor_set(v___x_865_, 0, v___x_920_);
v___x_926_ = v___x_865_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_920_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_927_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_927_, 3, v_l_698_);
lean_ctor_set(v_reuseFailAlloc_927_, 4, v___x_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_698_) == 0)
{
lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_958_; 
lean_inc_ref(v_l_698_);
lean_inc(v_v_697_);
lean_inc(v_k_696_);
lean_inc(v_size_695_);
v_isSharedCheck_958_ = !lean_is_exclusive(v_l_685_);
if (v_isSharedCheck_958_ == 0)
{
lean_object* v_unused_959_; lean_object* v_unused_960_; lean_object* v_unused_961_; lean_object* v_unused_962_; lean_object* v_unused_963_; 
v_unused_959_ = lean_ctor_get(v_l_685_, 4);
lean_dec(v_unused_959_);
v_unused_960_ = lean_ctor_get(v_l_685_, 3);
lean_dec(v_unused_960_);
v_unused_961_ = lean_ctor_get(v_l_685_, 2);
lean_dec(v_unused_961_);
v_unused_962_ = lean_ctor_get(v_l_685_, 1);
lean_dec(v_unused_962_);
v_unused_963_ = lean_ctor_get(v_l_685_, 0);
lean_dec(v_unused_963_);
v___x_936_ = v_l_685_;
v_isShared_937_ = v_isSharedCheck_958_;
goto v_resetjp_935_;
}
else
{
lean_dec(v_l_685_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_958_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
if (lean_obj_tag(v_r_699_) == 0)
{
lean_object* v_k_938_; lean_object* v_v_939_; lean_object* v_size_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v_k_938_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_k_938_);
v_v_939_ = lean_ctor_get(v___x_851_, 1);
lean_inc(v_v_939_);
lean_dec_ref(v___x_851_);
v_size_940_ = lean_ctor_get(v_r_699_, 0);
v___x_941_ = lean_nat_add(v___x_705_, v_size_695_);
lean_dec(v_size_695_);
v___x_942_ = lean_nat_add(v___x_705_, v_size_940_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 4, v_tree_852_);
lean_ctor_set(v___x_849_, 3, v_r_699_);
lean_ctor_set(v___x_849_, 2, v_v_939_);
lean_ctor_set(v___x_849_, 1, v_k_938_);
lean_ctor_set(v___x_849_, 0, v___x_942_);
v___x_944_ = v___x_849_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_k_938_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v_v_939_);
lean_ctor_set(v_reuseFailAlloc_948_, 3, v_r_699_);
lean_ctor_set(v_reuseFailAlloc_948_, 4, v_tree_852_);
v___x_944_ = v_reuseFailAlloc_948_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_946_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 4, v___x_944_);
lean_ctor_set(v___x_936_, 0, v___x_941_);
v___x_946_ = v___x_936_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_947_, 3, v_l_698_);
lean_ctor_set(v_reuseFailAlloc_947_, 4, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
else
{
lean_object* v_k_949_; lean_object* v_v_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
lean_dec(v_size_695_);
v_k_949_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_k_949_);
v_v_950_ = lean_ctor_get(v___x_851_, 1);
lean_inc(v_v_950_);
lean_dec_ref(v___x_851_);
v___x_951_ = lean_unsigned_to_nat(3u);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 4, v_r_699_);
lean_ctor_set(v___x_849_, 3, v_r_699_);
lean_ctor_set(v___x_849_, 2, v_v_950_);
lean_ctor_set(v___x_849_, 1, v_k_949_);
lean_ctor_set(v___x_849_, 0, v___x_705_);
v___x_953_ = v___x_849_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_k_949_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v_v_950_);
lean_ctor_set(v_reuseFailAlloc_957_, 3, v_r_699_);
lean_ctor_set(v_reuseFailAlloc_957_, 4, v_r_699_);
v___x_953_ = v_reuseFailAlloc_957_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_955_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 4, v___x_953_);
lean_ctor_set(v___x_936_, 0, v___x_951_);
v___x_955_ = v___x_936_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_956_, 3, v_l_698_);
lean_ctor_set(v_reuseFailAlloc_956_, 4, v___x_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_699_) == 0)
{
lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_988_; 
lean_inc(v_l_698_);
lean_inc(v_v_697_);
lean_inc(v_k_696_);
v_isSharedCheck_988_ = !lean_is_exclusive(v_l_685_);
if (v_isSharedCheck_988_ == 0)
{
lean_object* v_unused_989_; lean_object* v_unused_990_; lean_object* v_unused_991_; lean_object* v_unused_992_; lean_object* v_unused_993_; 
v_unused_989_ = lean_ctor_get(v_l_685_, 4);
lean_dec(v_unused_989_);
v_unused_990_ = lean_ctor_get(v_l_685_, 3);
lean_dec(v_unused_990_);
v_unused_991_ = lean_ctor_get(v_l_685_, 2);
lean_dec(v_unused_991_);
v_unused_992_ = lean_ctor_get(v_l_685_, 1);
lean_dec(v_unused_992_);
v_unused_993_ = lean_ctor_get(v_l_685_, 0);
lean_dec(v_unused_993_);
v___x_965_ = v_l_685_;
v_isShared_966_ = v_isSharedCheck_988_;
goto v_resetjp_964_;
}
else
{
lean_dec(v_l_685_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_988_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v_k_967_; lean_object* v_v_968_; lean_object* v_k_969_; lean_object* v_v_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_984_; 
v_k_967_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_k_967_);
v_v_968_ = lean_ctor_get(v___x_851_, 1);
lean_inc(v_v_968_);
lean_dec_ref(v___x_851_);
v_k_969_ = lean_ctor_get(v_r_699_, 1);
v_v_970_ = lean_ctor_get(v_r_699_, 2);
v_isSharedCheck_984_ = !lean_is_exclusive(v_r_699_);
if (v_isSharedCheck_984_ == 0)
{
lean_object* v_unused_985_; lean_object* v_unused_986_; lean_object* v_unused_987_; 
v_unused_985_ = lean_ctor_get(v_r_699_, 4);
lean_dec(v_unused_985_);
v_unused_986_ = lean_ctor_get(v_r_699_, 3);
lean_dec(v_unused_986_);
v_unused_987_ = lean_ctor_get(v_r_699_, 0);
lean_dec(v_unused_987_);
v___x_972_ = v_r_699_;
v_isShared_973_ = v_isSharedCheck_984_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_v_970_);
lean_inc(v_k_969_);
lean_dec(v_r_699_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_984_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_974_ = lean_unsigned_to_nat(3u);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 4, v_l_698_);
lean_ctor_set(v___x_972_, 3, v_l_698_);
lean_ctor_set(v___x_972_, 2, v_v_697_);
lean_ctor_set(v___x_972_, 1, v_k_696_);
lean_ctor_set(v___x_972_, 0, v___x_705_);
v___x_976_ = v___x_972_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_983_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_983_, 3, v_l_698_);
lean_ctor_set(v_reuseFailAlloc_983_, 4, v_l_698_);
v___x_976_ = v_reuseFailAlloc_983_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_978_; 
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 4, v_l_698_);
lean_ctor_set(v___x_849_, 3, v_l_698_);
lean_ctor_set(v___x_849_, 2, v_v_968_);
lean_ctor_set(v___x_849_, 1, v_k_967_);
lean_ctor_set(v___x_849_, 0, v___x_705_);
v___x_978_ = v___x_849_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_k_967_);
lean_ctor_set(v_reuseFailAlloc_982_, 2, v_v_968_);
lean_ctor_set(v_reuseFailAlloc_982_, 3, v_l_698_);
lean_ctor_set(v_reuseFailAlloc_982_, 4, v_l_698_);
v___x_978_ = v_reuseFailAlloc_982_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_980_; 
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 4, v___x_978_);
lean_ctor_set(v___x_965_, 3, v___x_976_);
lean_ctor_set(v___x_965_, 2, v_v_970_);
lean_ctor_set(v___x_965_, 1, v_k_969_);
lean_ctor_set(v___x_965_, 0, v___x_974_);
v___x_980_ = v___x_965_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_k_969_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v_v_970_);
lean_ctor_set(v_reuseFailAlloc_981_, 3, v___x_976_);
lean_ctor_set(v_reuseFailAlloc_981_, 4, v___x_978_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
}
}
else
{
lean_object* v_k_994_; lean_object* v_v_995_; lean_object* v___x_996_; lean_object* v___x_998_; 
v_k_994_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_k_994_);
v_v_995_ = lean_ctor_get(v___x_851_, 1);
lean_inc(v_v_995_);
lean_dec_ref(v___x_851_);
v___x_996_ = lean_unsigned_to_nat(2u);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 4, v_r_699_);
lean_ctor_set(v___x_849_, 3, v_l_685_);
lean_ctor_set(v___x_849_, 2, v_v_995_);
lean_ctor_set(v___x_849_, 1, v_k_994_);
lean_ctor_set(v___x_849_, 0, v___x_996_);
v___x_998_ = v___x_849_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_k_994_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v_v_995_);
lean_ctor_set(v_reuseFailAlloc_999_, 3, v_l_685_);
lean_ctor_set(v_reuseFailAlloc_999_, 4, v_r_699_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
}
}
else
{
return v_l_685_;
}
}
else
{
return v_r_686_;
}
}
else
{
lean_object* v_val_1006_; lean_object* v___x_1008_; 
v_val_1006_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_val_1006_);
lean_dec_ref_known(v___x_694_, 1);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 2, v_val_1006_);
lean_ctor_set(v___x_688_, 1, v_k_680_);
v___x_1008_ = v___x_688_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_size_682_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_k_680_);
lean_ctor_set(v_reuseFailAlloc_1009_, 2, v_val_1006_);
lean_ctor_set(v_reuseFailAlloc_1009_, 3, v_l_685_);
lean_ctor_set(v_reuseFailAlloc_1009_, 4, v_r_686_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
default: 
{
lean_object* v_impl_1010_; lean_object* v___x_1011_; 
lean_del_object(v___x_688_);
lean_dec(v_size_682_);
v_impl_1010_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_679_, v_k_680_, v_r_686_);
v___x_1011_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_683_, v_v_684_, v_l_685_, v_impl_1010_);
return v___x_1011_;
}
}
}
}
else
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_box(0);
v___x_1014_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_679_, v___x_1013_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_dec(v_k_680_);
return v_t_681_;
}
else
{
lean_object* v_val_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_val_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_val_1015_);
lean_dec_ref_known(v___x_1014_, 1);
v___x_1016_ = lean_unsigned_to_nat(1u);
v___x_1017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v_k_680_);
lean_ctor_set(v___x_1017_, 2, v_val_1015_);
lean_ctor_set(v___x_1017_, 3, v_t_681_);
lean_ctor_set(v___x_1017_, 4, v_t_681_);
return v___x_1017_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1018_, lean_object* v_i_1019_, lean_object* v_k_1020_){
_start:
{
lean_object* v___x_1021_; uint8_t v___x_1022_; 
v___x_1021_ = lean_array_get_size(v_keys_1018_);
v___x_1022_ = lean_nat_dec_lt(v_i_1019_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_dec(v_i_1019_);
return v___x_1022_;
}
else
{
lean_object* v_k_x27_1023_; uint8_t v___x_1024_; 
v_k_x27_1023_ = lean_array_fget_borrowed(v_keys_1018_, v_i_1019_);
v___x_1024_ = lean_name_eq(v_k_1020_, v_k_x27_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = lean_unsigned_to_nat(1u);
v___x_1026_ = lean_nat_add(v_i_1019_, v___x_1025_);
lean_dec(v_i_1019_);
v_i_1019_ = v___x_1026_;
goto _start;
}
else
{
lean_dec(v_i_1019_);
return v___x_1022_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1028_, lean_object* v_i_1029_, lean_object* v_k_1030_){
_start:
{
uint8_t v_res_1031_; lean_object* v_r_1032_; 
v_res_1031_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_1028_, v_i_1029_, v_k_1030_);
lean_dec(v_k_1030_);
lean_dec_ref(v_keys_1028_);
v_r_1032_ = lean_box(v_res_1031_);
return v_r_1032_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(lean_object* v_x_1033_, size_t v_x_1034_, lean_object* v_x_1035_){
_start:
{
if (lean_obj_tag(v_x_1033_) == 0)
{
lean_object* v_es_1036_; lean_object* v___x_1037_; size_t v___x_1038_; size_t v___x_1039_; lean_object* v_j_1040_; lean_object* v___x_1041_; 
v_es_1036_ = lean_ctor_get(v_x_1033_, 0);
v___x_1037_ = lean_box(2);
v___x_1038_ = ((size_t)31ULL);
v___x_1039_ = lean_usize_land(v_x_1034_, v___x_1038_);
v_j_1040_ = lean_usize_to_nat(v___x_1039_);
v___x_1041_ = lean_array_get_borrowed(v___x_1037_, v_es_1036_, v_j_1040_);
lean_dec(v_j_1040_);
switch(lean_obj_tag(v___x_1041_))
{
case 0:
{
lean_object* v_key_1042_; uint8_t v___x_1043_; 
v_key_1042_ = lean_ctor_get(v___x_1041_, 0);
v___x_1043_ = lean_name_eq(v_x_1035_, v_key_1042_);
return v___x_1043_;
}
case 1:
{
lean_object* v_node_1044_; size_t v___x_1045_; size_t v___x_1046_; 
v_node_1044_ = lean_ctor_get(v___x_1041_, 0);
v___x_1045_ = ((size_t)5ULL);
v___x_1046_ = lean_usize_shift_right(v_x_1034_, v___x_1045_);
v_x_1033_ = v_node_1044_;
v_x_1034_ = v___x_1046_;
goto _start;
}
default: 
{
uint8_t v___x_1048_; 
v___x_1048_ = 0;
return v___x_1048_;
}
}
}
else
{
lean_object* v_ks_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; 
v_ks_1049_ = lean_ctor_get(v_x_1033_, 0);
v___x_1050_ = lean_unsigned_to_nat(0u);
v___x_1051_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_ks_1049_, v___x_1050_, v_x_1035_);
return v___x_1051_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___boxed(lean_object* v_x_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_){
_start:
{
size_t v_x_3822__boxed_1055_; uint8_t v_res_1056_; lean_object* v_r_1057_; 
v_x_3822__boxed_1055_ = lean_unbox_usize(v_x_1053_);
lean_dec(v_x_1053_);
v_res_1056_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1052_, v_x_3822__boxed_1055_, v_x_1054_);
lean_dec(v_x_1054_);
lean_dec_ref(v_x_1052_);
v_r_1057_ = lean_box(v_res_1056_);
return v_r_1057_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(lean_object* v_x_1058_, lean_object* v_x_1059_){
_start:
{
uint64_t v___y_1061_; 
if (lean_obj_tag(v_x_1059_) == 0)
{
uint64_t v___x_1064_; 
v___x_1064_ = 1723ULL;
v___y_1061_ = v___x_1064_;
goto v___jp_1060_;
}
else
{
uint64_t v_hash_1065_; 
v_hash_1065_ = lean_ctor_get_uint64(v_x_1059_, sizeof(void*)*2);
v___y_1061_ = v_hash_1065_;
goto v___jp_1060_;
}
v___jp_1060_:
{
size_t v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = lean_uint64_to_usize(v___y_1061_);
v___x_1063_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1058_, v___x_1062_, v_x_1059_);
return v___x_1063_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(lean_object* v_x_1066_, lean_object* v_x_1067_){
_start:
{
uint8_t v_res_1068_; lean_object* v_r_1069_; 
v_res_1068_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_1066_, v_x_1067_);
lean_dec(v_x_1067_);
lean_dec_ref(v_x_1066_);
v_r_1069_ = lean_box(v_res_1068_);
return v_r_1069_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(lean_object* v_tactics_1070_, lean_object* v_a_1071_, uint8_t v___x_1072_, lean_object* v_x_1073_, lean_object* v_____s_1074_){
_start:
{
lean_object* v_fst_1075_; lean_object* v_kinds_1076_; uint8_t v___x_1077_; 
v_fst_1075_ = lean_ctor_get(v_x_1073_, 0);
lean_inc(v_fst_1075_);
lean_dec_ref(v_x_1073_);
v_kinds_1076_ = lean_ctor_get(v_tactics_1070_, 1);
v___x_1077_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_kinds_1076_, v_fst_1075_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; 
lean_dec(v_fst_1075_);
lean_dec(v_a_1071_);
v___x_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1078_, 0, v_____s_1074_);
return v___x_1078_;
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1079_ = l_Lean_Name_toString(v_a_1071_, v___x_1072_);
v___x_1080_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1079_, v_fst_1075_, v_____s_1074_);
v___x_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
return v___x_1081_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(lean_object* v_tactics_1082_, lean_object* v_a_1083_, lean_object* v___x_1084_, lean_object* v_x_1085_, lean_object* v_____s_1086_){
_start:
{
uint8_t v___x_3878__boxed_1087_; lean_object* v_res_1088_; 
v___x_3878__boxed_1087_ = lean_unbox(v___x_1084_);
v_res_1088_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(v_tactics_1082_, v_a_1083_, v___x_3878__boxed_1087_, v_x_1085_, v_____s_1086_);
lean_dec_ref(v_tactics_1082_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_f_1089_, lean_object* v_keys_1090_, lean_object* v_vals_1091_, lean_object* v_i_1092_, lean_object* v_acc_1093_){
_start:
{
lean_object* v___x_1094_; uint8_t v___x_1095_; 
v___x_1094_ = lean_array_get_size(v_keys_1090_);
v___x_1095_ = lean_nat_dec_lt(v_i_1092_, v___x_1094_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; 
lean_dec(v_i_1092_);
lean_dec_ref(v_f_1089_);
v___x_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1096_, 0, v_acc_1093_);
return v___x_1096_;
}
else
{
lean_object* v_k_1097_; lean_object* v_v_1098_; lean_object* v___x_1099_; 
v_k_1097_ = lean_array_fget_borrowed(v_keys_1090_, v_i_1092_);
v_v_1098_ = lean_array_fget_borrowed(v_vals_1091_, v_i_1092_);
lean_inc_ref(v_f_1089_);
lean_inc(v_v_1098_);
lean_inc(v_k_1097_);
v___x_1099_ = lean_apply_3(v_f_1089_, v_acc_1093_, v_k_1097_, v_v_1098_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_dec(v_i_1092_);
lean_dec_ref(v_f_1089_);
return v___x_1099_;
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v___x_1099_, 1);
v___x_1101_ = lean_unsigned_to_nat(1u);
v___x_1102_ = lean_nat_add(v_i_1092_, v___x_1101_);
lean_dec(v_i_1092_);
v_i_1092_ = v___x_1102_;
v_acc_1093_ = v_a_1100_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_f_1104_, lean_object* v_keys_1105_, lean_object* v_vals_1106_, lean_object* v_i_1107_, lean_object* v_acc_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1104_, v_keys_1105_, v_vals_1106_, v_i_1107_, v_acc_1108_);
lean_dec_ref(v_vals_1106_);
lean_dec_ref(v_keys_1105_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_f_1110_, lean_object* v_as_1111_, size_t v_i_1112_, size_t v_stop_1113_, lean_object* v_b_1114_){
_start:
{
lean_object* v_a_1116_; lean_object* v___y_1121_; uint8_t v___x_1123_; 
v___x_1123_ = lean_usize_dec_eq(v_i_1112_, v_stop_1113_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_array_uget_borrowed(v_as_1111_, v_i_1112_);
switch(lean_obj_tag(v___x_1124_))
{
case 0:
{
lean_object* v_key_1125_; lean_object* v_val_1126_; lean_object* v___x_1127_; 
v_key_1125_ = lean_ctor_get(v___x_1124_, 0);
v_val_1126_ = lean_ctor_get(v___x_1124_, 1);
lean_inc_ref(v_f_1110_);
lean_inc(v_val_1126_);
lean_inc(v_key_1125_);
v___x_1127_ = lean_apply_3(v_f_1110_, v_b_1114_, v_key_1125_, v_val_1126_);
v___y_1121_ = v___x_1127_;
goto v___jp_1120_;
}
case 1:
{
lean_object* v_node_1128_; lean_object* v___x_1129_; 
v_node_1128_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_node_1128_);
lean_inc_ref(v_f_1110_);
v___x_1129_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1110_, v_node_1128_, v_b_1114_);
v___y_1121_ = v___x_1129_;
goto v___jp_1120_;
}
default: 
{
v_a_1116_ = v_b_1114_;
goto v___jp_1115_;
}
}
}
else
{
lean_object* v___x_1130_; 
lean_dec_ref(v_f_1110_);
v___x_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1130_, 0, v_b_1114_);
return v___x_1130_;
}
v___jp_1115_:
{
size_t v___x_1117_; size_t v___x_1118_; 
v___x_1117_ = ((size_t)1ULL);
v___x_1118_ = lean_usize_add(v_i_1112_, v___x_1117_);
v_i_1112_ = v___x_1118_;
v_b_1114_ = v_a_1116_;
goto _start;
}
v___jp_1120_:
{
if (lean_obj_tag(v___y_1121_) == 0)
{
lean_dec_ref(v_f_1110_);
return v___y_1121_;
}
else
{
lean_object* v_a_1122_; 
v_a_1122_ = lean_ctor_get(v___y_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v___y_1121_, 1);
v_a_1116_ = v_a_1122_;
goto v___jp_1115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object* v_f_1131_, lean_object* v_x_1132_, lean_object* v_x_1133_){
_start:
{
if (lean_obj_tag(v_x_1132_) == 0)
{
lean_object* v_es_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1147_; 
v_es_1134_ = lean_ctor_get(v_x_1132_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_x_1132_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1136_ = v_x_1132_;
v_isShared_1137_ = v_isSharedCheck_1147_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_es_1134_);
lean_dec(v_x_1132_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1147_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1138_ = lean_unsigned_to_nat(0u);
v___x_1139_ = lean_array_get_size(v_es_1134_);
v___x_1140_ = lean_nat_dec_lt(v___x_1138_, v___x_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1142_; 
lean_dec_ref(v_es_1134_);
lean_dec_ref(v_f_1131_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set_tag(v___x_1136_, 1);
lean_ctor_set(v___x_1136_, 0, v_x_1133_);
v___x_1142_ = v___x_1136_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_x_1133_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
else
{
size_t v___x_1144_; size_t v___x_1145_; lean_object* v___x_1146_; 
lean_del_object(v___x_1136_);
v___x_1144_ = ((size_t)0ULL);
v___x_1145_ = lean_usize_of_nat(v___x_1139_);
v___x_1146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1131_, v_es_1134_, v___x_1144_, v___x_1145_, v_x_1133_);
lean_dec_ref(v_es_1134_);
return v___x_1146_;
}
}
}
else
{
lean_object* v_ks_1148_; lean_object* v_vs_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v_ks_1148_ = lean_ctor_get(v_x_1132_, 0);
lean_inc_ref(v_ks_1148_);
v_vs_1149_ = lean_ctor_get(v_x_1132_, 1);
lean_inc_ref(v_vs_1149_);
lean_dec_ref_known(v_x_1132_, 2);
v___x_1150_ = lean_unsigned_to_nat(0u);
v___x_1151_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1131_, v_ks_1148_, v_vs_1149_, v___x_1150_, v_x_1133_);
lean_dec_ref(v_vs_1149_);
lean_dec_ref(v_ks_1148_);
return v___x_1151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_f_1152_, lean_object* v_as_1153_, lean_object* v_i_1154_, lean_object* v_stop_1155_, lean_object* v_b_1156_){
_start:
{
size_t v_i_boxed_1157_; size_t v_stop_boxed_1158_; lean_object* v_res_1159_; 
v_i_boxed_1157_ = lean_unbox_usize(v_i_1154_);
lean_dec(v_i_1154_);
v_stop_boxed_1158_ = lean_unbox_usize(v_stop_1155_);
lean_dec(v_stop_1155_);
v_res_1159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1152_, v_as_1153_, v_i_boxed_1157_, v_stop_boxed_1158_, v_b_1156_);
lean_dec_ref(v_as_1153_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0(lean_object* v_f_1160_, lean_object* v_s_1161_, lean_object* v_a_1162_, lean_object* v_b_1163_){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1164_, 0, v_a_1162_);
lean_ctor_set(v___x_1164_, 1, v_b_1163_);
v___x_1165_ = lean_apply_2(v_f_1160_, v___x_1164_, v_s_1161_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1165_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1165_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(lean_object* v_map_1182_, lean_object* v_init_1183_, lean_object* v_f_1184_){
_start:
{
lean_object* v___f_1185_; lean_object* v___x_1186_; lean_object* v_a_1187_; 
v___f_1185_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1185_, 0, v_f_1184_);
lean_inc_ref(v_map_1182_);
v___x_1186_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v___f_1185_, v_map_1182_, v_init_1183_);
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref(v___x_1186_);
return v_a_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___boxed(lean_object* v_map_1188_, lean_object* v_init_1189_, lean_object* v_f_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_1188_, v_init_1189_, v_f_1190_);
lean_dec_ref(v_map_1188_);
return v_res_1191_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1192_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0);
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(lean_object* v_tactics_1195_, lean_object* v_a_1196_, uint8_t v___x_1197_, lean_object* v_as_x27_1198_, lean_object* v_b_1199_){
_start:
{
if (lean_obj_tag(v_as_x27_1198_) == 0)
{
lean_dec(v_a_1196_);
lean_dec_ref(v_tactics_1195_);
return v_b_1199_;
}
else
{
lean_object* v_head_1200_; lean_object* v_fst_1201_; lean_object* v_info_1202_; lean_object* v_tail_1203_; lean_object* v_collectKinds_1204_; lean_object* v___x_1205_; lean_object* v___f_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v_head_1200_ = lean_ctor_get(v_as_x27_1198_, 0);
v_fst_1201_ = lean_ctor_get(v_head_1200_, 0);
v_info_1202_ = lean_ctor_get(v_fst_1201_, 0);
v_tail_1203_ = lean_ctor_get(v_as_x27_1198_, 1);
v_collectKinds_1204_ = lean_ctor_get(v_info_1202_, 1);
v___x_1205_ = lean_box(v___x_1197_);
lean_inc(v_a_1196_);
lean_inc_ref(v_tactics_1195_);
v___f_1206_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1206_, 0, v_tactics_1195_);
lean_closure_set(v___f_1206_, 1, v_a_1196_);
lean_closure_set(v___f_1206_, 2, v___x_1205_);
v___x_1207_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1);
lean_inc_ref(v_collectKinds_1204_);
v___x_1208_ = lean_apply_1(v_collectKinds_1204_, v___x_1207_);
v___x_1209_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v___x_1208_, v_b_1199_, v___f_1206_);
lean_dec_ref(v___x_1208_);
v_as_x27_1198_ = v_tail_1203_;
v_b_1199_ = v___x_1209_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(lean_object* v_tactics_1211_, lean_object* v_a_1212_, lean_object* v___x_1213_, lean_object* v_as_x27_1214_, lean_object* v_b_1215_){
_start:
{
uint8_t v___x_4038__boxed_1216_; lean_object* v_res_1217_; 
v___x_4038__boxed_1216_ = lean_unbox(v___x_1213_);
v_res_1217_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1211_, v_a_1212_, v___x_4038__boxed_1216_, v_as_x27_1214_, v_b_1215_);
lean_dec(v_as_x27_1214_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(lean_object* v_tactics_1221_, lean_object* v_init_1222_, lean_object* v_x_1223_){
_start:
{
if (lean_obj_tag(v_x_1223_) == 0)
{
lean_object* v_k_1224_; lean_object* v_v_1225_; lean_object* v_l_1226_; lean_object* v_r_1227_; lean_object* v___x_1228_; lean_object* v_a_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; 
v_k_1224_ = lean_ctor_get(v_x_1223_, 1);
lean_inc(v_k_1224_);
v_v_1225_ = lean_ctor_get(v_x_1223_, 2);
lean_inc(v_v_1225_);
v_l_1226_ = lean_ctor_get(v_x_1223_, 3);
lean_inc(v_l_1226_);
v_r_1227_ = lean_ctor_get(v_x_1223_, 4);
lean_inc(v_r_1227_);
lean_dec_ref_known(v_x_1223_, 5);
lean_inc_ref(v_tactics_1221_);
v___x_1228_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_1221_, v_init_1222_, v_l_1226_);
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_a_1229_);
v___x_1230_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1));
v___x_1231_ = lean_name_eq(v_k_1224_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; 
lean_dec_ref(v___x_1228_);
lean_inc_ref(v_tactics_1221_);
v___x_1232_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1221_, v_k_1224_, v___x_1231_, v_v_1225_, v_a_1229_);
lean_dec(v_v_1225_);
v_init_1222_ = v___x_1232_;
v_x_1223_ = v_r_1227_;
goto _start;
}
else
{
lean_object* v_a_1234_; 
lean_dec(v_a_1229_);
lean_dec(v_v_1225_);
lean_dec(v_k_1224_);
v_a_1234_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_a_1234_);
lean_dec_ref(v___x_1228_);
v_init_1222_ = v_a_1234_;
v_x_1223_ = v_r_1227_;
goto _start;
}
}
else
{
lean_object* v___x_1236_; 
lean_dec_ref(v_tactics_1221_);
v___x_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1236_, 0, v_init_1222_);
return v___x_1236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(lean_object* v_tactics_1237_, lean_object* v_table_1238_, lean_object* v_firsts_1239_){
_start:
{
lean_object* v___x_1240_; lean_object* v_a_1241_; 
v___x_1240_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_1237_, v_firsts_1239_, v_table_1238_);
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
lean_dec_ref(v___x_1240_);
return v_a_1241_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_object* v_00_u03b2_1242_, lean_object* v_x_1243_, lean_object* v_x_1244_){
_start:
{
uint8_t v___x_1245_; 
v___x_1245_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_1243_, v_x_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(lean_object* v_00_u03b2_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_){
_start:
{
uint8_t v_res_1249_; lean_object* v_r_1250_; 
v_res_1249_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(v_00_u03b2_1246_, v_x_1247_, v_x_1248_);
lean_dec(v_x_1248_);
lean_dec_ref(v_x_1247_);
v_r_1250_ = lean_box(v_res_1249_);
return v_r_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(lean_object* v___x_1251_, lean_object* v_k_1252_, lean_object* v_t_1253_, lean_object* v_hl_1254_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1251_, v_k_1252_, v_t_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(lean_object* v_00_u03c3_1256_, lean_object* v_00_u03b2_1257_, lean_object* v_map_1258_, lean_object* v_init_1259_, lean_object* v_f_1260_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_1258_, v_init_1259_, v_f_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___boxed(lean_object* v_00_u03c3_1262_, lean_object* v_00_u03b2_1263_, lean_object* v_map_1264_, lean_object* v_init_1265_, lean_object* v_f_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(v_00_u03c3_1262_, v_00_u03b2_1263_, v_map_1264_, v_init_1265_, v_f_1266_);
lean_dec_ref(v_map_1264_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(lean_object* v_tactics_1268_, lean_object* v_a_1269_, uint8_t v___x_1270_, lean_object* v_as_1271_, lean_object* v_as_x27_1272_, lean_object* v_b_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1268_, v_a_1269_, v___x_1270_, v_as_x27_1272_, v_b_1273_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(lean_object* v_tactics_1276_, lean_object* v_a_1277_, lean_object* v___x_1278_, lean_object* v_as_1279_, lean_object* v_as_x27_1280_, lean_object* v_b_1281_, lean_object* v_a_1282_){
_start:
{
uint8_t v___x_4121__boxed_1283_; lean_object* v_res_1284_; 
v___x_4121__boxed_1283_ = lean_unbox(v___x_1278_);
v_res_1284_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(v_tactics_1276_, v_a_1277_, v___x_4121__boxed_1283_, v_as_1279_, v_as_x27_1280_, v_b_1281_, v_a_1282_);
lean_dec(v_as_x27_1280_);
lean_dec(v_as_1279_);
return v_res_1284_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_object* v_00_u03b2_1285_, lean_object* v_x_1286_, size_t v_x_1287_, lean_object* v_x_1288_){
_start:
{
uint8_t v___x_1289_; 
v___x_1289_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1286_, v_x_1287_, v_x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1290_, lean_object* v_x_1291_, lean_object* v_x_1292_, lean_object* v_x_1293_){
_start:
{
size_t v_x_4130__boxed_1294_; uint8_t v_res_1295_; lean_object* v_r_1296_; 
v_x_4130__boxed_1294_ = lean_unbox_usize(v_x_1292_);
lean_dec(v_x_1292_);
v_res_1295_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(v_00_u03b2_1290_, v_x_1291_, v_x_4130__boxed_1294_, v_x_1293_);
lean_dec(v_x_1293_);
lean_dec_ref(v_x_1291_);
v_r_1296_ = lean_box(v_res_1295_);
return v_r_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(lean_object* v_map_1297_, lean_object* v_f_1298_, lean_object* v_init_1299_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1298_, v_map_1297_, v_init_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(lean_object* v_00_u03c3_1301_, lean_object* v_00_u03c3_1302_, lean_object* v_00_u03b2_1303_, lean_object* v_map_1304_, lean_object* v_f_1305_, lean_object* v_init_1306_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1305_, v_map_1304_, v_init_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1308_, lean_object* v_keys_1309_, lean_object* v_vals_1310_, lean_object* v_heq_1311_, lean_object* v_i_1312_, lean_object* v_k_1313_){
_start:
{
uint8_t v___x_1314_; 
v___x_1314_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_1309_, v_i_1312_, v_k_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1315_, lean_object* v_keys_1316_, lean_object* v_vals_1317_, lean_object* v_heq_1318_, lean_object* v_i_1319_, lean_object* v_k_1320_){
_start:
{
uint8_t v_res_1321_; lean_object* v_r_1322_; 
v_res_1321_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(v_00_u03b2_1315_, v_keys_1316_, v_vals_1317_, v_heq_1318_, v_i_1319_, v_k_1320_);
lean_dec(v_k_1320_);
lean_dec_ref(v_vals_1317_);
lean_dec_ref(v_keys_1316_);
v_r_1322_ = lean_box(v_res_1321_);
return v_r_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(lean_object* v_00_u03c3_1323_, lean_object* v_00_u03c3_1324_, lean_object* v_00_u03b1_1325_, lean_object* v_00_u03b2_1326_, lean_object* v_f_1327_, lean_object* v_x_1328_, lean_object* v_x_1329_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1327_, v_x_1328_, v_x_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b1_1331_, lean_object* v_00_u03b2_1332_, lean_object* v_00_u03c3_1333_, lean_object* v_00_u03c3_1334_, lean_object* v_f_1335_, lean_object* v_as_1336_, size_t v_i_1337_, size_t v_stop_1338_, lean_object* v_b_1339_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1335_, v_as_1336_, v_i_1337_, v_stop_1338_, v_b_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1341_, lean_object* v_00_u03b2_1342_, lean_object* v_00_u03c3_1343_, lean_object* v_00_u03c3_1344_, lean_object* v_f_1345_, lean_object* v_as_1346_, lean_object* v_i_1347_, lean_object* v_stop_1348_, lean_object* v_b_1349_){
_start:
{
size_t v_i_boxed_1350_; size_t v_stop_boxed_1351_; lean_object* v_res_1352_; 
v_i_boxed_1350_ = lean_unbox_usize(v_i_1347_);
lean_dec(v_i_1347_);
v_stop_boxed_1351_ = lean_unbox_usize(v_stop_1348_);
lean_dec(v_stop_1348_);
v_res_1352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(v_00_u03b1_1341_, v_00_u03b2_1342_, v_00_u03c3_1343_, v_00_u03c3_1344_, v_f_1345_, v_as_1346_, v_i_boxed_1350_, v_stop_boxed_1351_, v_b_1349_);
lean_dec_ref(v_as_1346_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03c3_1353_, lean_object* v_00_u03c3_1354_, lean_object* v_00_u03b1_1355_, lean_object* v_00_u03b2_1356_, lean_object* v_f_1357_, lean_object* v_keys_1358_, lean_object* v_vals_1359_, lean_object* v_heq_1360_, lean_object* v_i_1361_, lean_object* v_acc_1362_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1357_, v_keys_1358_, v_vals_1359_, v_i_1361_, v_acc_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03c3_1364_, lean_object* v_00_u03c3_1365_, lean_object* v_00_u03b1_1366_, lean_object* v_00_u03b2_1367_, lean_object* v_f_1368_, lean_object* v_keys_1369_, lean_object* v_vals_1370_, lean_object* v_heq_1371_, lean_object* v_i_1372_, lean_object* v_acc_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(v_00_u03c3_1364_, v_00_u03c3_1365_, v_00_u03b1_1366_, v_00_u03b2_1367_, v_f_1368_, v_keys_1369_, v_vals_1370_, v_heq_1371_, v_i_1372_, v_acc_1373_);
lean_dec_ref(v_vals_1370_);
lean_dec_ref(v_keys_1369_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(lean_object* v_x1_1375_, lean_object* v_x2_1376_){
_start:
{
lean_object* v_fst_1377_; lean_object* v_snd_1378_; lean_object* v___x_1379_; 
v_fst_1377_ = lean_ctor_get(v_x2_1376_, 0);
lean_inc(v_fst_1377_);
v_snd_1378_ = lean_ctor_get(v_x2_1376_, 1);
lean_inc(v_snd_1378_);
lean_dec_ref(v_x2_1376_);
v___x_1379_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1377_, v_snd_1378_, v_x1_1375_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(lean_object* v___f_1399_, lean_object* v_x1_1400_, lean_object* v_x2_1401_){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v___x_1402_ = lean_unsigned_to_nat(0u);
v___x_1403_ = lean_array_get_size(v_x2_1401_);
v___x_1404_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_1405_ = lean_nat_dec_lt(v___x_1402_, v___x_1403_);
if (v___x_1405_ == 0)
{
lean_dec_ref(v_x2_1401_);
lean_dec_ref(v___f_1399_);
return v_x1_1400_;
}
else
{
uint8_t v___x_1406_; 
v___x_1406_ = lean_nat_dec_le(v___x_1403_, v___x_1403_);
if (v___x_1406_ == 0)
{
if (v___x_1405_ == 0)
{
lean_dec_ref(v_x2_1401_);
lean_dec_ref(v___f_1399_);
return v_x1_1400_;
}
else
{
size_t v___x_1407_; size_t v___x_1408_; lean_object* v___x_1409_; 
v___x_1407_ = ((size_t)0ULL);
v___x_1408_ = lean_usize_of_nat(v___x_1403_);
v___x_1409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1404_, v___f_1399_, v_x2_1401_, v___x_1407_, v___x_1408_, v_x1_1400_);
return v___x_1409_;
}
}
else
{
size_t v___x_1410_; size_t v___x_1411_; lean_object* v___x_1412_; 
v___x_1410_ = ((size_t)0ULL);
v___x_1411_ = lean_usize_of_nat(v___x_1403_);
v___x_1412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1404_, v___f_1399_, v_x2_1401_, v___x_1410_, v___x_1411_, v_x1_1400_);
return v___x_1412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object* v___x_1416_, lean_object* v___x_1417_, lean_object* v___x_1418_, lean_object* v___x_1419_, lean_object* v___x_1420_, lean_object* v_toPure_1421_, lean_object* v___f_1422_, lean_object* v_env_1423_){
_start:
{
lean_object* v___x_1424_; lean_object* v_ext_1425_; lean_object* v_toEnvExtension_1426_; lean_object* v_asyncMode_1427_; lean_object* v___x_1428_; lean_object* v_categories_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1424_ = l_Lean_Parser_parserExtension;
v_ext_1425_ = lean_ctor_get(v___x_1424_, 1);
v_toEnvExtension_1426_ = lean_ctor_get(v_ext_1425_, 0);
v_asyncMode_1427_ = lean_ctor_get(v_toEnvExtension_1426_, 2);
lean_inc_ref(v_env_1423_);
v___x_1428_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1416_, v___x_1424_, v_env_1423_, v_asyncMode_1427_);
v_categories_1429_ = lean_ctor_get(v___x_1428_, 2);
lean_inc_ref(v_categories_1429_);
lean_dec(v___x_1428_);
v___x_1430_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_1431_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_1417_, v___x_1418_, v_categories_1429_, v___x_1430_);
lean_dec_ref(v_categories_1429_);
if (lean_obj_tag(v___x_1431_) == 1)
{
lean_object* v_val_1432_; lean_object* v___y_1434_; lean_object* v___x_1441_; lean_object* v_toEnvExtension_1442_; lean_object* v_exportEntriesFn_1443_; lean_object* v_asyncMode_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v_importedEntries_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v_exported_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; 
v_val_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_val_1432_);
lean_dec_ref_known(v___x_1431_, 1);
v___x_1441_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1442_ = lean_ctor_get(v___x_1441_, 0);
v_exportEntriesFn_1443_ = lean_ctor_get(v___x_1441_, 4);
v_asyncMode_1444_ = lean_ctor_get(v_toEnvExtension_1442_, 2);
v___x_1445_ = lean_box(0);
lean_inc_ref_n(v_env_1423_, 2);
v___x_1446_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1419_, v_toEnvExtension_1442_, v_env_1423_, v_asyncMode_1444_, v___x_1445_);
v_importedEntries_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc_ref(v_importedEntries_1447_);
lean_dec(v___x_1446_);
v___x_1448_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1420_, v___x_1441_, v_env_1423_, v_asyncMode_1444_, v___x_1445_);
lean_inc_ref(v_exportEntriesFn_1443_);
v___x_1449_ = lean_apply_2(v_exportEntriesFn_1443_, v_env_1423_, v___x_1448_);
v_exported_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_exported_1450_);
lean_dec_ref(v___x_1449_);
v___x_1451_ = lean_box(1);
v___x_1452_ = lean_array_push(v_importedEntries_1447_, v_exported_1450_);
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = lean_array_get_size(v___x_1452_);
v___x_1455_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_1456_ = lean_nat_dec_lt(v___x_1453_, v___x_1454_);
if (v___x_1456_ == 0)
{
lean_dec_ref(v___x_1452_);
lean_dec_ref(v___f_1422_);
v___y_1434_ = v___x_1451_;
goto v___jp_1433_;
}
else
{
uint8_t v___x_1457_; 
v___x_1457_ = lean_nat_dec_le(v___x_1454_, v___x_1454_);
if (v___x_1457_ == 0)
{
if (v___x_1456_ == 0)
{
lean_dec_ref(v___x_1452_);
lean_dec_ref(v___f_1422_);
v___y_1434_ = v___x_1451_;
goto v___jp_1433_;
}
else
{
size_t v___x_1458_; size_t v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = ((size_t)0ULL);
v___x_1459_ = lean_usize_of_nat(v___x_1454_);
v___x_1460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1455_, v___f_1422_, v___x_1452_, v___x_1458_, v___x_1459_, v___x_1451_);
v___y_1434_ = v___x_1460_;
goto v___jp_1433_;
}
}
else
{
size_t v___x_1461_; size_t v___x_1462_; lean_object* v___x_1463_; 
v___x_1461_ = ((size_t)0ULL);
v___x_1462_ = lean_usize_of_nat(v___x_1454_);
v___x_1463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1455_, v___f_1422_, v___x_1452_, v___x_1461_, v___x_1462_, v___x_1451_);
v___y_1434_ = v___x_1463_;
goto v___jp_1433_;
}
}
v___jp_1433_:
{
lean_object* v_tables_1435_; lean_object* v_leadingTable_1436_; lean_object* v_trailingTable_1437_; lean_object* v_firstTokens_1438_; lean_object* v_firstTokens_1439_; lean_object* v___x_1440_; 
v_tables_1435_ = lean_ctor_get(v_val_1432_, 2);
v_leadingTable_1436_ = lean_ctor_get(v_tables_1435_, 0);
v_trailingTable_1437_ = lean_ctor_get(v_tables_1435_, 2);
lean_inc(v_trailingTable_1437_);
lean_inc(v_leadingTable_1436_);
lean_inc(v_val_1432_);
v_firstTokens_1438_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_1432_, v_leadingTable_1436_, v___y_1434_);
v_firstTokens_1439_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_1432_, v_trailingTable_1437_, v_firstTokens_1438_);
v___x_1440_ = lean_apply_2(v_toPure_1421_, lean_box(0), v_firstTokens_1439_);
return v___x_1440_;
}
}
else
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
lean_dec(v___x_1431_);
lean_dec_ref(v_env_1423_);
lean_dec_ref(v___f_1422_);
lean_dec(v___x_1420_);
v___x_1464_ = lean_box(1);
v___x_1465_ = lean_apply_2(v_toPure_1421_, lean_box(0), v___x_1464_);
return v___x_1465_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed(lean_object* v___x_1466_, lean_object* v___x_1467_, lean_object* v___x_1468_, lean_object* v___x_1469_, lean_object* v___x_1470_, lean_object* v_toPure_1471_, lean_object* v___f_1472_, lean_object* v_env_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(v___x_1466_, v___x_1467_, v___x_1468_, v___x_1469_, v___x_1470_, v_toPure_1471_, v___f_1472_, v_env_1473_);
lean_dec_ref(v___x_1469_);
lean_dec_ref(v___x_1466_);
return v_res_1474_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2(void){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1478_ = lean_box(1);
v___x_1479_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object* v_inst_1482_, lean_object* v_inst_1483_){
_start:
{
lean_object* v_toApplicative_1484_; lean_object* v_toBind_1485_; lean_object* v_getEnv_1486_; lean_object* v_toPure_1487_; lean_object* v___f_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___f_1494_; lean_object* v___x_1495_; 
v_toApplicative_1484_ = lean_ctor_get(v_inst_1482_, 0);
lean_inc_ref(v_toApplicative_1484_);
v_toBind_1485_ = lean_ctor_get(v_inst_1482_, 1);
lean_inc(v_toBind_1485_);
lean_dec_ref(v_inst_1482_);
v_getEnv_1486_ = lean_ctor_get(v_inst_1483_, 0);
lean_inc(v_getEnv_1486_);
lean_dec_ref(v_inst_1483_);
v_toPure_1487_ = lean_ctor_get(v_toApplicative_1484_, 1);
lean_inc(v_toPure_1487_);
lean_dec_ref(v_toApplicative_1484_);
v___f_1488_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1));
v___x_1489_ = lean_box(1);
v___x_1490_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_1491_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_1492_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___x_1493_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___f_1494_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1494_, 0, v___x_1493_);
lean_closure_set(v___f_1494_, 1, v___x_1491_);
lean_closure_set(v___f_1494_, 2, v___x_1492_);
lean_closure_set(v___f_1494_, 3, v___x_1490_);
lean_closure_set(v___f_1494_, 4, v___x_1489_);
lean_closure_set(v___f_1494_, 5, v_toPure_1487_);
lean_closure_set(v___f_1494_, 6, v___f_1488_);
v___x_1495_ = lean_apply_4(v_toBind_1485_, lean_box(0), lean_box(0), v_getEnv_1486_, v___f_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object* v_m_1496_, lean_object* v_inst_1497_, lean_object* v_inst_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(v_inst_1497_, v_inst_1498_);
return v___x_1499_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1500_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0);
v___x_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1501_);
return v___x_1502_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1503_ = lean_box(1);
v___x_1504_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4);
v___x_1505_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1);
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
v___x_1527_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__3));
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
v___x_1517_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2);
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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object* v_s_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0));
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object* v_s_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v_s_1580_);
lean_dec_ref(v_s_1580_);
return v_res_1581_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t v___x_1582_, lean_object* v_x1_1583_, lean_object* v_x2_1584_){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v___x_1585_ = l_Lean_Name_toString(v_x1_1583_, v___x_1582_);
v___x_1586_ = l_Lean_Name_toString(v_x2_1584_, v___x_1582_);
v___x_1587_ = lean_string_dec_lt(v___x_1585_, v___x_1586_);
lean_dec_ref(v___x_1586_);
lean_dec_ref(v___x_1585_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object* v___x_1588_, lean_object* v_x1_1589_, lean_object* v_x2_1590_){
_start:
{
uint8_t v___x_16883__boxed_1591_; uint8_t v_res_1592_; lean_object* v_r_1593_; 
v___x_16883__boxed_1591_ = lean_unbox(v___x_1588_);
v_res_1592_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_16883__boxed_1591_, v_x1_1589_, v_x2_1590_);
v_r_1593_ = lean_box(v_res_1592_);
return v_r_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(lean_object* v_hi_1594_, lean_object* v_pivot_1595_, lean_object* v_as_1596_, lean_object* v_i_1597_, lean_object* v_k_1598_){
_start:
{
uint8_t v___x_1599_; 
v___x_1599_ = lean_nat_dec_lt(v_k_1598_, v_hi_1594_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
lean_dec(v_k_1598_);
lean_dec(v_pivot_1595_);
v___x_1600_ = lean_array_fswap(v_as_1596_, v_i_1597_, v_hi_1594_);
v___x_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1601_, 0, v_i_1597_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
return v___x_1601_;
}
else
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; 
v___x_1602_ = lean_array_fget_borrowed(v_as_1596_, v_k_1598_);
lean_inc(v___x_1602_);
v___x_1603_ = l_Lean_Name_toString(v___x_1602_, v___x_1599_);
lean_inc(v_pivot_1595_);
v___x_1604_ = l_Lean_Name_toString(v_pivot_1595_, v___x_1599_);
v___x_1605_ = lean_string_dec_lt(v___x_1603_, v___x_1604_);
lean_dec_ref(v___x_1604_);
lean_dec_ref(v___x_1603_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = lean_unsigned_to_nat(1u);
v___x_1607_ = lean_nat_add(v_k_1598_, v___x_1606_);
lean_dec(v_k_1598_);
v_k_1598_ = v___x_1607_;
goto _start;
}
else
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1609_ = lean_array_fswap(v_as_1596_, v_i_1597_, v_k_1598_);
v___x_1610_ = lean_unsigned_to_nat(1u);
v___x_1611_ = lean_nat_add(v_i_1597_, v___x_1610_);
lean_dec(v_i_1597_);
v___x_1612_ = lean_nat_add(v_k_1598_, v___x_1610_);
lean_dec(v_k_1598_);
v_as_1596_ = v___x_1609_;
v_i_1597_ = v___x_1611_;
v_k_1598_ = v___x_1612_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg___boxed(lean_object* v_hi_1614_, lean_object* v_pivot_1615_, lean_object* v_as_1616_, lean_object* v_i_1617_, lean_object* v_k_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_1614_, v_pivot_1615_, v_as_1616_, v_i_1617_, v_k_1618_);
lean_dec(v_hi_1614_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object* v_n_1620_, lean_object* v_as_1621_, lean_object* v_lo_1622_, lean_object* v_hi_1623_){
_start:
{
lean_object* v___y_1625_; uint8_t v___x_1635_; 
v___x_1635_ = lean_nat_dec_lt(v_lo_1622_, v_hi_1623_);
if (v___x_1635_ == 0)
{
lean_dec(v_lo_1622_);
return v_as_1621_;
}
else
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v_mid_1638_; lean_object* v___y_1640_; lean_object* v___y_1646_; lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v___x_1636_ = lean_nat_add(v_lo_1622_, v_hi_1623_);
v___x_1637_ = lean_unsigned_to_nat(1u);
v_mid_1638_ = lean_nat_shiftr(v___x_1636_, v___x_1637_);
lean_dec(v___x_1636_);
v___x_1651_ = lean_array_fget_borrowed(v_as_1621_, v_mid_1638_);
v___x_1652_ = lean_array_fget_borrowed(v_as_1621_, v_lo_1622_);
lean_inc(v___x_1652_);
lean_inc(v___x_1651_);
v___x_1653_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1635_, v___x_1651_, v___x_1652_);
if (v___x_1653_ == 0)
{
v___y_1646_ = v_as_1621_;
goto v___jp_1645_;
}
else
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_array_fswap(v_as_1621_, v_lo_1622_, v_mid_1638_);
v___y_1646_ = v___x_1654_;
goto v___jp_1645_;
}
v___jp_1639_:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; 
v___x_1641_ = lean_array_fget_borrowed(v___y_1640_, v_mid_1638_);
v___x_1642_ = lean_array_fget_borrowed(v___y_1640_, v_hi_1623_);
lean_inc(v___x_1642_);
lean_inc(v___x_1641_);
v___x_1643_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1635_, v___x_1641_, v___x_1642_);
if (v___x_1643_ == 0)
{
lean_dec(v_mid_1638_);
v___y_1625_ = v___y_1640_;
goto v___jp_1624_;
}
else
{
lean_object* v___x_1644_; 
v___x_1644_ = lean_array_fswap(v___y_1640_, v_mid_1638_, v_hi_1623_);
lean_dec(v_mid_1638_);
v___y_1625_ = v___x_1644_;
goto v___jp_1624_;
}
}
v___jp_1645_:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; 
v___x_1647_ = lean_array_fget_borrowed(v___y_1646_, v_hi_1623_);
v___x_1648_ = lean_array_fget_borrowed(v___y_1646_, v_lo_1622_);
lean_inc(v___x_1648_);
lean_inc(v___x_1647_);
v___x_1649_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1635_, v___x_1647_, v___x_1648_);
if (v___x_1649_ == 0)
{
v___y_1640_ = v___y_1646_;
goto v___jp_1639_;
}
else
{
lean_object* v___x_1650_; 
v___x_1650_ = lean_array_fswap(v___y_1646_, v_lo_1622_, v_hi_1623_);
v___y_1640_ = v___x_1650_;
goto v___jp_1639_;
}
}
}
v___jp_1624_:
{
lean_object* v_pivot_1626_; lean_object* v___x_1627_; lean_object* v_fst_1628_; lean_object* v_snd_1629_; uint8_t v___x_1630_; 
v_pivot_1626_ = lean_array_fget(v___y_1625_, v_hi_1623_);
lean_inc_n(v_lo_1622_, 2);
v___x_1627_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_1623_, v_pivot_1626_, v___y_1625_, v_lo_1622_, v_lo_1622_);
v_fst_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_fst_1628_);
v_snd_1629_ = lean_ctor_get(v___x_1627_, 1);
lean_inc(v_snd_1629_);
lean_dec_ref(v___x_1627_);
v___x_1630_ = lean_nat_dec_le(v_hi_1623_, v_fst_1628_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1631_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_1620_, v_snd_1629_, v_lo_1622_, v_fst_1628_);
v___x_1632_ = lean_unsigned_to_nat(1u);
v___x_1633_ = lean_nat_add(v_fst_1628_, v___x_1632_);
lean_dec(v_fst_1628_);
v_as_1621_ = v___x_1631_;
v_lo_1622_ = v___x_1633_;
goto _start;
}
else
{
lean_dec(v_fst_1628_);
lean_dec(v_lo_1622_);
return v_snd_1629_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object* v_n_1655_, lean_object* v_as_1656_, lean_object* v_lo_1657_, lean_object* v_hi_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_1655_, v_as_1656_, v_lo_1657_, v_hi_1658_);
lean_dec(v_hi_1658_);
lean_dec(v_n_1655_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(lean_object* v_init_1660_, lean_object* v_x_1661_){
_start:
{
if (lean_obj_tag(v_x_1661_) == 0)
{
lean_object* v_k_1662_; lean_object* v_l_1663_; lean_object* v_r_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v_k_1662_ = lean_ctor_get(v_x_1661_, 1);
lean_inc(v_k_1662_);
v_l_1663_ = lean_ctor_get(v_x_1661_, 3);
lean_inc(v_l_1663_);
v_r_1664_ = lean_ctor_get(v_x_1661_, 4);
lean_inc(v_r_1664_);
lean_dec_ref_known(v_x_1661_, 5);
v___x_1665_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_1660_, v_l_1663_);
v___x_1666_ = lean_array_push(v___x_1665_, v_k_1662_);
v_init_1660_ = v___x_1666_;
v_x_1661_ = v_r_1664_;
goto _start;
}
else
{
return v_init_1660_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object* v_a_1668_, lean_object* v_a_1669_){
_start:
{
if (lean_obj_tag(v_a_1668_) == 0)
{
lean_object* v___x_1670_; 
v___x_1670_ = l_List_reverse___redArg(v_a_1669_);
return v___x_1670_;
}
else
{
lean_object* v_head_1671_; lean_object* v_tail_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1681_; 
v_head_1671_ = lean_ctor_get(v_a_1668_, 0);
v_tail_1672_ = lean_ctor_get(v_a_1668_, 1);
v_isSharedCheck_1681_ = !lean_is_exclusive(v_a_1668_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1674_ = v_a_1668_;
v_isShared_1675_ = v_isSharedCheck_1681_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_tail_1672_);
lean_inc(v_head_1671_);
lean_dec(v_a_1668_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1681_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1676_ = l_Lean_Level_param___override(v_head_1671_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 1, v_a_1669_);
lean_ctor_set(v___x_1674_, 0, v___x_1676_);
v___x_1678_ = v___x_1674_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1676_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_a_1669_);
v___x_1678_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
v_a_1668_ = v_tail_1672_;
v_a_1669_ = v___x_1678_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object* v_x1_1682_, lean_object* v_x2_1683_){
_start:
{
lean_object* v_fst_1684_; lean_object* v_fst_1685_; uint8_t v___x_1686_; 
v_fst_1684_ = lean_ctor_get(v_x1_1682_, 0);
v_fst_1685_ = lean_ctor_get(v_x2_1683_, 0);
v___x_1686_ = l_Lean_Name_quickLt(v_fst_1684_, v_fst_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_x1_1687_, lean_object* v_x2_1688_){
_start:
{
uint8_t v_res_1689_; lean_object* v_r_1690_; 
v_res_1689_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_x1_1687_, v_x2_1688_);
lean_dec_ref(v_x2_1688_);
lean_dec_ref(v_x1_1687_);
v_r_1690_ = lean_box(v_res_1689_);
return v_r_1690_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object* v_as_1691_, lean_object* v_k_1692_, lean_object* v_x_1693_, lean_object* v_x_1694_){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v_m_1697_; lean_object* v_a_1698_; uint8_t v___x_1699_; 
v___x_1695_ = lean_nat_add(v_x_1693_, v_x_1694_);
v___x_1696_ = lean_unsigned_to_nat(1u);
v_m_1697_ = lean_nat_shiftr(v___x_1695_, v___x_1696_);
lean_dec(v___x_1695_);
v_a_1698_ = lean_array_fget_borrowed(v_as_1691_, v_m_1697_);
v___x_1699_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_a_1698_, v_k_1692_);
if (v___x_1699_ == 0)
{
uint8_t v___x_1700_; 
lean_dec(v_x_1694_);
v___x_1700_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_k_1692_, v_a_1698_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; 
lean_dec(v_m_1697_);
lean_dec(v_x_1693_);
lean_inc(v_a_1698_);
v___x_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1701_, 0, v_a_1698_);
return v___x_1701_;
}
else
{
lean_object* v___x_1702_; uint8_t v___x_1703_; lean_object* v___x_1704_; uint8_t v___y_1706_; 
v___x_1702_ = lean_unsigned_to_nat(0u);
v___x_1703_ = lean_nat_dec_eq(v_m_1697_, v___x_1702_);
v___x_1704_ = lean_nat_sub(v_m_1697_, v___x_1696_);
lean_dec(v_m_1697_);
if (v___x_1703_ == 0)
{
uint8_t v___x_1709_; 
v___x_1709_ = lean_nat_dec_lt(v___x_1704_, v_x_1693_);
v___y_1706_ = v___x_1709_;
goto v___jp_1705_;
}
else
{
v___y_1706_ = v___x_1703_;
goto v___jp_1705_;
}
v___jp_1705_:
{
if (v___y_1706_ == 0)
{
v_x_1694_ = v___x_1704_;
goto _start;
}
else
{
lean_object* v___x_1708_; 
lean_dec(v___x_1704_);
lean_dec(v_x_1693_);
v___x_1708_ = lean_box(0);
return v___x_1708_;
}
}
}
}
else
{
lean_object* v___x_1710_; uint8_t v___x_1711_; 
lean_dec(v_x_1693_);
v___x_1710_ = lean_nat_add(v_m_1697_, v___x_1696_);
lean_dec(v_m_1697_);
v___x_1711_ = lean_nat_dec_le(v___x_1710_, v_x_1694_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; 
lean_dec(v___x_1710_);
lean_dec(v_x_1694_);
v___x_1712_ = lean_box(0);
return v___x_1712_;
}
else
{
v_x_1693_ = v___x_1710_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_as_1714_, lean_object* v_k_1715_, lean_object* v_x_1716_, lean_object* v_x_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_1714_, v_k_1715_, v_x_1716_, v_x_1717_);
lean_dec_ref(v_k_1715_);
lean_dec_ref(v_as_1714_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object* v_tac_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v___x_1723_; lean_object* v_env_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1723_ = lean_st_ref_get(v___y_1721_);
v_env_1727_ = lean_ctor_get(v___x_1723_, 0);
lean_inc_ref(v_env_1727_);
lean_dec(v___x_1723_);
v___x_1728_ = lean_box(1);
v___x_1729_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1727_, v_tac_1720_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v___x_1730_; lean_object* v_toEnvExtension_1731_; lean_object* v_asyncMode_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1730_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1731_ = lean_ctor_get(v___x_1730_, 0);
v_asyncMode_1732_ = lean_ctor_get(v_toEnvExtension_1731_, 2);
v___x_1733_ = lean_box(0);
v___x_1734_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1728_, v___x_1730_, v_env_1727_, v_asyncMode_1732_, v___x_1733_);
v___x_1735_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1734_, v_tac_1720_);
lean_dec(v_tac_1720_);
lean_dec(v___x_1734_);
v___x_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
return v___x_1736_;
}
else
{
lean_object* v_val_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1765_; 
v_val_1737_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1739_ = v___x_1729_;
v_isShared_1740_ = v_isSharedCheck_1765_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_val_1737_);
lean_dec(v___x_1729_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1765_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1741_; uint8_t v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1741_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_1742_ = 0;
v___x_1743_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1728_, v___x_1741_, v_env_1727_, v_val_1737_, v___x_1742_);
lean_dec(v_val_1737_);
lean_dec_ref(v_env_1727_);
v___x_1744_ = lean_unsigned_to_nat(0u);
v___x_1745_ = lean_array_get_size(v___x_1743_);
v___x_1746_ = lean_nat_dec_lt(v___x_1744_, v___x_1745_);
if (v___x_1746_ == 0)
{
lean_dec_ref(v___x_1743_);
lean_del_object(v___x_1739_);
lean_dec(v_tac_1720_);
goto v___jp_1724_;
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v___x_1747_ = lean_unsigned_to_nat(1u);
v___x_1748_ = lean_nat_sub(v___x_1745_, v___x_1747_);
v___x_1749_ = lean_nat_dec_le(v___x_1744_, v___x_1748_);
if (v___x_1749_ == 0)
{
lean_dec(v___x_1748_);
lean_dec_ref(v___x_1743_);
lean_del_object(v___x_1739_);
lean_dec(v_tac_1720_);
goto v___jp_1724_;
}
else
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1750_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
v___x_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1751_, 0, v_tac_1720_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
v___x_1752_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v___x_1743_, v___x_1751_, v___x_1744_, v___x_1748_);
lean_dec_ref_known(v___x_1751_, 2);
lean_dec_ref(v___x_1743_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_del_object(v___x_1739_);
goto v___jp_1724_;
}
else
{
lean_object* v_val_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1764_; 
v_val_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1764_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_val_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1764_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v_snd_1757_; lean_object* v___x_1759_; 
v_snd_1757_ = lean_ctor_get(v_val_1753_, 1);
lean_inc(v_snd_1757_);
lean_dec(v_val_1753_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v_snd_1757_);
v___x_1759_ = v___x_1755_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_snd_1757_);
v___x_1759_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_object* v___x_1761_; 
if (v_isShared_1740_ == 0)
{
lean_ctor_set_tag(v___x_1739_, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1759_);
v___x_1761_ = v___x_1739_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
}
}
}
}
v___jp_1724_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = lean_box(0);
v___x_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
return v___x_1726_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object* v_tac_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_1766_, v___y_1767_);
lean_dec(v___y_1767_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object* v_t_1770_, lean_object* v_k_1771_){
_start:
{
if (lean_obj_tag(v_t_1770_) == 0)
{
lean_object* v_k_1772_; lean_object* v_v_1773_; lean_object* v_l_1774_; lean_object* v_r_1775_; uint8_t v___x_1776_; 
v_k_1772_ = lean_ctor_get(v_t_1770_, 1);
v_v_1773_ = lean_ctor_get(v_t_1770_, 2);
v_l_1774_ = lean_ctor_get(v_t_1770_, 3);
v_r_1775_ = lean_ctor_get(v_t_1770_, 4);
v___x_1776_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1771_, v_k_1772_);
switch(v___x_1776_)
{
case 0:
{
v_t_1770_ = v_l_1774_;
goto _start;
}
case 1:
{
lean_object* v___x_1778_; 
lean_inc(v_v_1773_);
v___x_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1778_, 0, v_v_1773_);
return v___x_1778_;
}
default: 
{
v_t_1770_ = v_r_1775_;
goto _start;
}
}
}
else
{
lean_object* v___x_1780_; 
v___x_1780_ = lean_box(0);
return v___x_1780_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg___boxed(lean_object* v_t_1781_, lean_object* v_k_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_1781_, v_k_1782_);
lean_dec(v_k_1782_);
lean_dec(v_t_1781_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(lean_object* v_a_1784_, lean_object* v_x_1785_){
_start:
{
if (lean_obj_tag(v_x_1785_) == 0)
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_box(0);
return v___x_1786_;
}
else
{
lean_object* v_key_1787_; lean_object* v_value_1788_; lean_object* v_tail_1789_; uint8_t v___x_1790_; 
v_key_1787_ = lean_ctor_get(v_x_1785_, 0);
v_value_1788_ = lean_ctor_get(v_x_1785_, 1);
v_tail_1789_ = lean_ctor_get(v_x_1785_, 2);
v___x_1790_ = lean_name_eq(v_key_1787_, v_a_1784_);
if (v___x_1790_ == 0)
{
v_x_1785_ = v_tail_1789_;
goto _start;
}
else
{
lean_object* v___x_1792_; 
lean_inc(v_value_1788_);
v___x_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1792_, 0, v_value_1788_);
return v___x_1792_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg___boxed(lean_object* v_a_1793_, lean_object* v_x_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_1793_, v_x_1794_);
lean_dec(v_x_1794_);
lean_dec(v_a_1793_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(lean_object* v_m_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v_buckets_1798_; lean_object* v___x_1799_; uint64_t v___y_1801_; 
v_buckets_1798_ = lean_ctor_get(v_m_1796_, 1);
v___x_1799_ = lean_array_get_size(v_buckets_1798_);
if (lean_obj_tag(v_a_1797_) == 0)
{
uint64_t v___x_1815_; 
v___x_1815_ = 1723ULL;
v___y_1801_ = v___x_1815_;
goto v___jp_1800_;
}
else
{
uint64_t v_hash_1816_; 
v_hash_1816_ = lean_ctor_get_uint64(v_a_1797_, sizeof(void*)*2);
v___y_1801_ = v_hash_1816_;
goto v___jp_1800_;
}
v___jp_1800_:
{
uint64_t v___x_1802_; uint64_t v___x_1803_; uint64_t v_fold_1804_; uint64_t v___x_1805_; uint64_t v___x_1806_; uint64_t v___x_1807_; size_t v___x_1808_; size_t v___x_1809_; size_t v___x_1810_; size_t v___x_1811_; size_t v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1802_ = 32ULL;
v___x_1803_ = lean_uint64_shift_right(v___y_1801_, v___x_1802_);
v_fold_1804_ = lean_uint64_xor(v___y_1801_, v___x_1803_);
v___x_1805_ = 16ULL;
v___x_1806_ = lean_uint64_shift_right(v_fold_1804_, v___x_1805_);
v___x_1807_ = lean_uint64_xor(v_fold_1804_, v___x_1806_);
v___x_1808_ = lean_uint64_to_usize(v___x_1807_);
v___x_1809_ = lean_usize_of_nat(v___x_1799_);
v___x_1810_ = ((size_t)1ULL);
v___x_1811_ = lean_usize_sub(v___x_1809_, v___x_1810_);
v___x_1812_ = lean_usize_land(v___x_1808_, v___x_1811_);
v___x_1813_ = lean_array_uget_borrowed(v_buckets_1798_, v___x_1812_);
v___x_1814_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_1797_, v___x_1813_);
return v___x_1814_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg___boxed(lean_object* v_m_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_1817_, v_a_1818_);
lean_dec(v_a_1818_);
lean_dec_ref(v_m_1817_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_keys_1820_, lean_object* v_vals_1821_, lean_object* v_i_1822_, lean_object* v_k_1823_){
_start:
{
lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1824_ = lean_array_get_size(v_keys_1820_);
v___x_1825_ = lean_nat_dec_lt(v_i_1822_, v___x_1824_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; 
lean_dec(v_i_1822_);
v___x_1826_ = lean_box(0);
return v___x_1826_;
}
else
{
lean_object* v_k_x27_1827_; uint8_t v___x_1828_; 
v_k_x27_1827_ = lean_array_fget_borrowed(v_keys_1820_, v_i_1822_);
v___x_1828_ = lean_name_eq(v_k_1823_, v_k_x27_1827_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = lean_unsigned_to_nat(1u);
v___x_1830_ = lean_nat_add(v_i_1822_, v___x_1829_);
lean_dec(v_i_1822_);
v_i_1822_ = v___x_1830_;
goto _start;
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = lean_array_fget_borrowed(v_vals_1821_, v_i_1822_);
lean_dec(v_i_1822_);
lean_inc(v___x_1832_);
v___x_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
return v___x_1833_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object* v_keys_1834_, lean_object* v_vals_1835_, lean_object* v_i_1836_, lean_object* v_k_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_1834_, v_vals_1835_, v_i_1836_, v_k_1837_);
lean_dec(v_k_1837_);
lean_dec_ref(v_vals_1835_);
lean_dec_ref(v_keys_1834_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object* v_x_1839_, size_t v_x_1840_, lean_object* v_x_1841_){
_start:
{
if (lean_obj_tag(v_x_1839_) == 0)
{
lean_object* v_es_1842_; lean_object* v___x_1843_; size_t v___x_1844_; size_t v___x_1845_; lean_object* v_j_1846_; lean_object* v___x_1847_; 
v_es_1842_ = lean_ctor_get(v_x_1839_, 0);
v___x_1843_ = lean_box(2);
v___x_1844_ = ((size_t)31ULL);
v___x_1845_ = lean_usize_land(v_x_1840_, v___x_1844_);
v_j_1846_ = lean_usize_to_nat(v___x_1845_);
v___x_1847_ = lean_array_get_borrowed(v___x_1843_, v_es_1842_, v_j_1846_);
lean_dec(v_j_1846_);
switch(lean_obj_tag(v___x_1847_))
{
case 0:
{
lean_object* v_key_1848_; lean_object* v_val_1849_; uint8_t v___x_1850_; 
v_key_1848_ = lean_ctor_get(v___x_1847_, 0);
v_val_1849_ = lean_ctor_get(v___x_1847_, 1);
v___x_1850_ = lean_name_eq(v_x_1841_, v_key_1848_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; 
v___x_1851_ = lean_box(0);
return v___x_1851_;
}
else
{
lean_object* v___x_1852_; 
lean_inc(v_val_1849_);
v___x_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1852_, 0, v_val_1849_);
return v___x_1852_;
}
}
case 1:
{
lean_object* v_node_1853_; size_t v___x_1854_; size_t v___x_1855_; 
v_node_1853_ = lean_ctor_get(v___x_1847_, 0);
v___x_1854_ = ((size_t)5ULL);
v___x_1855_ = lean_usize_shift_right(v_x_1840_, v___x_1854_);
v_x_1839_ = v_node_1853_;
v_x_1840_ = v___x_1855_;
goto _start;
}
default: 
{
lean_object* v___x_1857_; 
v___x_1857_ = lean_box(0);
return v___x_1857_;
}
}
}
else
{
lean_object* v_ks_1858_; lean_object* v_vs_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v_ks_1858_ = lean_ctor_get(v_x_1839_, 0);
v_vs_1859_ = lean_ctor_get(v_x_1839_, 1);
v___x_1860_ = lean_unsigned_to_nat(0u);
v___x_1861_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_ks_1858_, v_vs_1859_, v___x_1860_, v_x_1841_);
return v___x_1861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_1862_, lean_object* v_x_1863_, lean_object* v_x_1864_){
_start:
{
size_t v_x_17258__boxed_1865_; lean_object* v_res_1866_; 
v_x_17258__boxed_1865_ = lean_unbox_usize(v_x_1863_);
lean_dec(v_x_1863_);
v_res_1866_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1862_, v_x_17258__boxed_1865_, v_x_1864_);
lean_dec(v_x_1864_);
lean_dec_ref(v_x_1862_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object* v_x_1867_, lean_object* v_x_1868_){
_start:
{
uint64_t v___y_1870_; 
if (lean_obj_tag(v_x_1868_) == 0)
{
uint64_t v___x_1873_; 
v___x_1873_ = 1723ULL;
v___y_1870_ = v___x_1873_;
goto v___jp_1869_;
}
else
{
uint64_t v_hash_1874_; 
v_hash_1874_ = lean_ctor_get_uint64(v_x_1868_, sizeof(void*)*2);
v___y_1870_ = v_hash_1874_;
goto v___jp_1869_;
}
v___jp_1869_:
{
size_t v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = lean_uint64_to_usize(v___y_1870_);
v___x_1872_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1867_, v___x_1871_, v_x_1868_);
return v___x_1872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object* v_x_1875_, lean_object* v_x_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_1875_, v_x_1876_);
lean_dec(v_x_1876_);
lean_dec_ref(v_x_1875_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object* v_x_1878_, lean_object* v_x_1879_){
_start:
{
uint8_t v_stage_u2081_1880_; 
v_stage_u2081_1880_ = lean_ctor_get_uint8(v_x_1878_, sizeof(void*)*2);
if (v_stage_u2081_1880_ == 0)
{
lean_object* v_map_u2081_1881_; lean_object* v_map_u2082_1882_; lean_object* v___x_1883_; 
v_map_u2081_1881_ = lean_ctor_get(v_x_1878_, 0);
v_map_u2082_1882_ = lean_ctor_get(v_x_1878_, 1);
v___x_1883_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_1881_, v_x_1879_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_map_u2082_1882_, v_x_1879_);
return v___x_1884_;
}
else
{
return v___x_1883_;
}
}
else
{
lean_object* v_map_u2081_1885_; lean_object* v___x_1886_; 
v_map_u2081_1885_ = lean_ctor_get(v_x_1878_, 0);
v___x_1886_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_1885_, v_x_1879_);
return v___x_1886_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg___boxed(lean_object* v_x_1887_, lean_object* v_x_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_1887_, v_x_1888_);
lean_dec(v_x_1888_);
lean_dec_ref(v_x_1887_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object* v_firsts_1890_, lean_object* v_n_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1910_; lean_object* v_val_1911_; lean_object* v___x_1913_; lean_object* v___y_1915_; lean_object* v_env_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1913_ = lean_st_ref_get(v___y_1893_);
v_env_1930_ = lean_ctor_get(v___x_1913_, 0);
lean_inc_ref(v_env_1930_);
lean_dec(v___x_1913_);
v___x_1931_ = l_Lean_Environment_constants(v_env_1930_);
v___x_1932_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v___x_1931_, v_n_1891_);
lean_dec_ref(v___x_1931_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v___x_1933_; 
v___x_1933_ = lean_box(0);
v___y_1915_ = v___x_1933_;
goto v___jp_1914_;
}
else
{
lean_object* v_val_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v_val_1934_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_val_1934_);
lean_dec_ref_known(v___x_1932_, 1);
v___x_1935_ = l_Lean_ConstantInfo_levelParams(v_val_1934_);
lean_dec(v_val_1934_);
v___x_1936_ = lean_box(0);
v___x_1937_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(v___x_1935_, v___x_1936_);
v___y_1915_ = v___x_1937_;
goto v___jp_1914_;
}
v___jp_1895_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; uint8_t v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1898_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8);
v___x_1899_ = l_Lean_Expr_const___override(v_n_1891_, v___y_1896_);
v___x_1900_ = lean_unsigned_to_nat(32u);
v___x_1901_ = lean_mk_empty_array_with_capacity(v___x_1900_);
lean_dec_ref(v___x_1901_);
v___x_1902_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2);
v___x_1903_ = lean_box(0);
v___x_1904_ = 0;
v___x_1905_ = l_Lean_MessageData_withExprHover(v___y_1897_, v___x_1899_, v___x_1902_, v___x_1903_, v___x_1903_, v___x_1903_, v___x_1904_);
v___x_1906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1898_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
lean_ctor_set(v___x_1907_, 1, v___x_1898_);
v___x_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
return v___x_1908_;
}
v___jp_1909_:
{
lean_object* v___x_1912_; 
v___x_1912_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1912_, 0, v_val_1911_);
v___y_1896_ = v___y_1910_;
v___y_1897_ = v___x_1912_;
goto v___jp_1895_;
}
v___jp_1914_:
{
lean_object* v___x_1916_; lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1929_; 
lean_inc(v_n_1891_);
v___x_1916_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_n_1891_, v___y_1893_);
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1919_ = v___x_1916_;
v_isShared_1920_ = v_isSharedCheck_1929_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1929_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
if (lean_obj_tag(v_a_1917_) == 0)
{
lean_object* v___x_1921_; 
v___x_1921_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_firsts_1890_, v_n_1891_);
if (lean_obj_tag(v___x_1921_) == 0)
{
uint8_t v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1922_ = 1;
lean_inc(v_n_1891_);
v___x_1923_ = l_Lean_Name_toString(v_n_1891_, v___x_1922_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set_tag(v___x_1919_, 3);
lean_ctor_set(v___x_1919_, 0, v___x_1923_);
v___x_1925_ = v___x_1919_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
v___y_1896_ = v___y_1915_;
v___y_1897_ = v___x_1925_;
goto v___jp_1895_;
}
}
else
{
lean_object* v_val_1927_; 
lean_del_object(v___x_1919_);
v_val_1927_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_val_1927_);
lean_dec_ref_known(v___x_1921_, 1);
v___y_1910_ = v___y_1915_;
v_val_1911_ = v_val_1927_;
goto v___jp_1909_;
}
}
else
{
lean_object* v_val_1928_; 
lean_del_object(v___x_1919_);
v_val_1928_ = lean_ctor_get(v_a_1917_, 0);
lean_inc(v_val_1928_);
lean_dec_ref_known(v_a_1917_, 1);
v___y_1910_ = v___y_1915_;
v_val_1911_ = v_val_1928_;
goto v___jp_1909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object* v_firsts_1938_, lean_object* v_n_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_firsts_1938_, v_n_1939_, v___y_1940_, v___y_1941_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v_firsts_1938_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object* v_a_1944_, lean_object* v_x_1945_, lean_object* v_x_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
if (lean_obj_tag(v_x_1945_) == 0)
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = l_List_reverse___redArg(v_x_1946_);
v___x_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
return v___x_1951_;
}
else
{
lean_object* v_head_1952_; lean_object* v_tail_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1971_; 
v_head_1952_ = lean_ctor_get(v_x_1945_, 0);
v_tail_1953_ = lean_ctor_get(v_x_1945_, 1);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_x_1945_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1955_ = v_x_1945_;
v_isShared_1956_ = v_isSharedCheck_1971_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_tail_1953_);
lean_inc(v_head_1952_);
lean_dec(v_x_1945_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1971_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1957_; 
v___x_1957_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_a_1944_, v_head_1952_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v___x_1960_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1957_, 1);
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 1, v_x_1946_);
lean_ctor_set(v___x_1955_, 0, v_a_1958_);
v___x_1960_ = v___x_1955_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1958_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v_x_1946_);
v___x_1960_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
v_x_1945_ = v_tail_1953_;
v_x_1946_ = v___x_1960_;
goto _start;
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_del_object(v___x_1955_);
lean_dec(v_tail_1953_);
lean_dec(v_x_1946_);
v_a_1963_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1957_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1957_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object* v_a_1972_, lean_object* v_x_1973_, lean_object* v_x_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_1972_, v_x_1973_, v_x_1974_, v___y_1975_, v___y_1976_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v_a_1972_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object* v_val_1979_, lean_object* v___x_1980_, lean_object* v___x_1981_, lean_object* v_a_1982_, lean_object* v_b_1983_){
_start:
{
lean_object* v_it_1985_; lean_object* v_startInclusive_1986_; lean_object* v_endExclusive_1987_; 
if (lean_obj_tag(v_a_1982_) == 0)
{
lean_object* v_currPos_1992_; lean_object* v_searcher_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2016_; 
v_currPos_1992_ = lean_ctor_get(v_a_1982_, 0);
v_searcher_1993_ = lean_ctor_get(v_a_1982_, 1);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_a_1982_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_1995_ = v_a_1982_;
v_isShared_1996_ = v_isSharedCheck_2016_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_searcher_1993_);
lean_inc(v_currPos_1992_);
lean_dec(v_a_1982_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2016_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
uint8_t v_decide_1997_; 
v_decide_1997_ = lean_nat_dec_eq(v_searcher_1993_, v___x_1981_);
if (v_decide_1997_ == 0)
{
uint32_t v___x_1998_; uint32_t v___x_1999_; uint8_t v___x_2000_; 
v___x_1998_ = 10;
v___x_1999_ = lean_string_utf8_get_fast(v_val_1979_, v_searcher_1993_);
v___x_2000_ = lean_uint32_dec_eq(v___x_1999_, v___x_1998_);
if (v___x_2000_ == 0)
{
lean_object* v___x_2001_; lean_object* v___x_2003_; 
v___x_2001_ = lean_string_utf8_next_fast(v_val_1979_, v_searcher_1993_);
lean_dec(v_searcher_1993_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 1, v___x_2001_);
v___x_2003_ = v___x_1995_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_currPos_1992_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v___x_2001_);
v___x_2003_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
v_a_1982_ = v___x_2003_;
goto _start;
}
}
else
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v_slice_2009_; lean_object* v_nextIt_2011_; 
v___x_2006_ = lean_string_utf8_next_fast(v_val_1979_, v_searcher_1993_);
v___x_2007_ = lean_nat_sub(v___x_2006_, v_searcher_1993_);
v___x_2008_ = lean_nat_add(v_searcher_1993_, v___x_2007_);
lean_dec(v___x_2007_);
v_slice_2009_ = l_String_Slice_subslice_x21(v___x_1980_, v_currPos_1992_, v_searcher_1993_);
lean_inc(v___x_2008_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 1, v___x_2008_);
lean_ctor_set(v___x_1995_, 0, v___x_2008_);
v_nextIt_2011_ = v___x_1995_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v___x_2008_);
v_nextIt_2011_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v_startInclusive_2012_; lean_object* v_endExclusive_2013_; 
v_startInclusive_2012_ = lean_ctor_get(v_slice_2009_, 0);
lean_inc(v_startInclusive_2012_);
v_endExclusive_2013_ = lean_ctor_get(v_slice_2009_, 1);
lean_inc(v_endExclusive_2013_);
lean_dec_ref(v_slice_2009_);
v_it_1985_ = v_nextIt_2011_;
v_startInclusive_1986_ = v_startInclusive_2012_;
v_endExclusive_1987_ = v_endExclusive_2013_;
goto v___jp_1984_;
}
}
}
else
{
lean_object* v___x_2015_; 
lean_del_object(v___x_1995_);
lean_dec(v_searcher_1993_);
v___x_2015_ = lean_box(1);
lean_inc(v___x_1981_);
v_it_1985_ = v___x_2015_;
v_startInclusive_1986_ = v_currPos_1992_;
v_endExclusive_1987_ = v___x_1981_;
goto v___jp_1984_;
}
}
}
else
{
lean_dec(v___x_1981_);
return v_b_1983_;
}
v___jp_1984_:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1988_ = lean_string_utf8_extract_fast(v_val_1979_, v_startInclusive_1986_, v_endExclusive_1987_);
lean_dec(v_endExclusive_1987_);
lean_dec(v_startInclusive_1986_);
v___x_1989_ = l_Lean_stringToMessageData(v___x_1988_);
v___x_1990_ = lean_array_push(v_b_1983_, v___x_1989_);
v_a_1982_ = v_it_1985_;
v_b_1983_ = v___x_1990_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object* v_val_2017_, lean_object* v___x_2018_, lean_object* v___x_2019_, lean_object* v_a_2020_, lean_object* v_b_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2017_, v___x_2018_, v___x_2019_, v_a_2020_, v_b_2021_);
lean_dec_ref(v___x_2018_);
lean_dec_ref(v_val_2017_);
return v_res_2022_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2(void){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1));
v___x_2027_ = l_Lean_stringToMessageData(v___x_2026_);
return v___x_2027_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4(void){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3));
v___x_2030_ = l_Lean_stringToMessageData(v___x_2029_);
return v___x_2030_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6(void){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5));
v___x_2033_ = l_Lean_stringToMessageData(v___x_2032_);
return v___x_2033_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9(void){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8));
v___x_2038_ = l_Lean_MessageData_ofFormat(v___x_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_x_2041_, lean_object* v_x_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
if (lean_obj_tag(v_x_2041_) == 0)
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = l_List_reverse___redArg(v_x_2042_);
v___x_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
return v___x_2047_;
}
else
{
lean_object* v_head_2048_; lean_object* v_tail_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2146_; 
v_head_2048_ = lean_ctor_get(v_x_2041_, 0);
v_tail_2049_ = lean_ctor_get(v_x_2041_, 1);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_x_2041_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2051_ = v_x_2041_;
v_isShared_2052_ = v_isSharedCheck_2146_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_tail_2049_);
lean_inc(v_head_2048_);
lean_dec(v_x_2041_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2146_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v_snd_2066_; lean_object* v_fst_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2145_; 
v_snd_2066_ = lean_ctor_get(v_head_2048_, 1);
v_fst_2067_ = lean_ctor_get(v_head_2048_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v_head_2048_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2069_ = v_head_2048_;
v_isShared_2070_ = v_isSharedCheck_2145_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_snd_2066_);
lean_inc(v_fst_2067_);
lean_dec(v_head_2048_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2145_;
goto v_resetjp_2068_;
}
v___jp_2053_:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2063_; 
v___x_2058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___y_2054_);
lean_ctor_set(v___x_2058_, 1, v___y_2057_);
v___x_2059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
lean_ctor_set(v___x_2059_, 1, v___y_2056_);
v___x_2060_ = l_Lean_MessageData_nestD(v___x_2059_);
lean_inc_ref(v___y_2055_);
v___x_2061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___y_2055_);
lean_ctor_set(v___x_2061_, 1, v___x_2060_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 1, v_x_2042_);
lean_ctor_set(v___x_2051_, 0, v___x_2061_);
v___x_2063_ = v___x_2051_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2061_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v_x_2042_);
v___x_2063_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
v_x_2041_ = v_tail_2049_;
v_x_2042_ = v___x_2063_;
goto _start;
}
}
v_resetjp_2068_:
{
lean_object* v_fst_2071_; lean_object* v_snd_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2144_; 
v_fst_2071_ = lean_ctor_get(v_snd_2066_, 0);
v_snd_2072_ = lean_ctor_get(v_snd_2066_, 1);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_snd_2066_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2074_ = v_snd_2066_;
v_isShared_2075_ = v_isSharedCheck_2144_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_snd_2072_);
lean_inc(v_fst_2071_);
lean_dec(v_snd_2066_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2144_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v_a_2099_; lean_object* v___y_2115_; lean_object* v___x_2124_; 
v___x_2124_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2040_, v_fst_2067_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lean_MessageData_nil;
v_a_2099_ = v___x_2125_;
goto v___jp_2098_;
}
else
{
lean_object* v_val_2126_; 
v_val_2126_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_val_2126_);
lean_dec_ref_known(v___x_2124_, 1);
if (lean_obj_tag(v_val_2126_) == 0)
{
lean_object* v_size_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___x_2135_; uint8_t v___x_2136_; 
v_size_2127_ = lean_ctor_get(v_val_2126_, 0);
v___x_2128_ = lean_mk_empty_array_with_capacity(v_size_2127_);
v___x_2129_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v___x_2128_, v_val_2126_);
v___x_2130_ = lean_array_get_size(v___x_2129_);
v___x_2135_ = lean_unsigned_to_nat(0u);
v___x_2136_ = lean_nat_dec_eq(v___x_2130_, v___x_2135_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___y_2140_; uint8_t v___x_2142_; 
v___x_2137_ = lean_unsigned_to_nat(1u);
v___x_2138_ = lean_nat_sub(v___x_2130_, v___x_2137_);
v___x_2142_ = lean_nat_dec_le(v___x_2135_, v___x_2138_);
if (v___x_2142_ == 0)
{
lean_inc(v___x_2138_);
v___y_2140_ = v___x_2138_;
goto v___jp_2139_;
}
else
{
v___y_2140_ = v___x_2135_;
goto v___jp_2139_;
}
v___jp_2139_:
{
uint8_t v___x_2141_; 
v___x_2141_ = lean_nat_dec_le(v___y_2140_, v___x_2138_);
if (v___x_2141_ == 0)
{
lean_dec(v___x_2138_);
lean_inc(v___y_2140_);
v___y_2132_ = v___y_2140_;
v___y_2133_ = v___y_2140_;
goto v___jp_2131_;
}
else
{
v___y_2132_ = v___y_2140_;
v___y_2133_ = v___x_2138_;
goto v___jp_2131_;
}
}
}
else
{
v___y_2115_ = v___x_2129_;
goto v___jp_2114_;
}
v___jp_2131_:
{
lean_object* v___x_2134_; 
v___x_2134_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v___x_2130_, v___x_2129_, v___y_2132_, v___y_2133_);
lean_dec(v___y_2133_);
v___y_2115_ = v___x_2134_;
goto v___jp_2114_;
}
}
else
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_MessageData_nil;
v_a_2099_ = v___x_2143_;
goto v___jp_2098_;
}
}
v___jp_2076_:
{
lean_object* v___x_2082_; 
if (v_isShared_2075_ == 0)
{
lean_ctor_set_tag(v___x_2074_, 7);
lean_ctor_set(v___x_2074_, 1, v___y_2080_);
lean_ctor_set(v___x_2074_, 0, v___y_2077_);
v___x_2082_ = v___x_2074_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___y_2077_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v___y_2080_);
v___x_2082_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
if (lean_obj_tag(v_snd_2072_) == 0)
{
lean_object* v___x_2083_; 
lean_del_object(v___x_2069_);
v___x_2083_ = l_Lean_MessageData_nil;
v___y_2054_ = v___x_2082_;
v___y_2055_ = v___y_2078_;
v___y_2056_ = v___y_2079_;
v___y_2057_ = v___x_2083_;
goto v___jp_2053_;
}
else
{
lean_object* v_val_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2095_; 
v_val_2084_ = lean_ctor_get(v_snd_2072_, 0);
lean_inc_n(v_val_2084_, 2);
lean_dec_ref_known(v_snd_2072_, 1);
v___x_2085_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2086_ = lean_unsigned_to_nat(0u);
v___x_2087_ = lean_string_utf8_byte_size(v_val_2084_);
v___x_2088_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2088_, 0, v_val_2084_);
lean_ctor_set(v___x_2088_, 1, v___x_2086_);
lean_ctor_set(v___x_2088_, 2, v___x_2087_);
v___x_2089_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v___x_2088_);
v___x_2090_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0));
v___x_2091_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2084_, v___x_2088_, v___x_2087_, v___x_2089_, v___x_2090_);
lean_dec_ref_known(v___x_2088_, 3);
lean_dec(v_val_2084_);
v___x_2092_ = lean_array_to_list(v___x_2091_);
v___x_2093_ = l_Lean_MessageData_joinSep(v___x_2092_, v___x_2085_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set_tag(v___x_2069_, 7);
lean_ctor_set(v___x_2069_, 1, v___x_2093_);
lean_ctor_set(v___x_2069_, 0, v___x_2085_);
v___x_2095_ = v___x_2069_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2085_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
v___y_2054_ = v___x_2082_;
v___y_2055_ = v___y_2078_;
v___y_2056_ = v___y_2079_;
v___y_2057_ = v___x_2095_;
goto v___jp_2053_;
}
}
}
}
v___jp_2098_:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; uint8_t v___x_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; 
v___x_2100_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2);
v___x_2101_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8);
lean_inc(v_fst_2067_);
v___x_2102_ = l_Lean_MessageData_ofName(v_fst_2067_);
v___x_2103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2101_);
lean_ctor_set(v___x_2103_, 1, v___x_2102_);
v___x_2104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2103_);
lean_ctor_set(v___x_2104_, 1, v___x_2101_);
v___x_2105_ = 1;
v___x_2106_ = l_Lean_Name_toString(v_fst_2067_, v___x_2105_);
v___x_2107_ = lean_string_dec_eq(v___x_2106_, v_fst_2071_);
lean_dec_ref(v___x_2106_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2108_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4);
v___x_2109_ = l_Lean_stringToMessageData(v_fst_2071_);
v___x_2110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2108_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
v___x_2111_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6);
v___x_2112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2110_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___y_2077_ = v___x_2104_;
v___y_2078_ = v___x_2100_;
v___y_2079_ = v_a_2099_;
v___y_2080_ = v___x_2112_;
goto v___jp_2076_;
}
else
{
lean_object* v___x_2113_; 
lean_dec(v_fst_2071_);
v___x_2113_ = l_Lean_MessageData_nil;
v___y_2077_ = v___x_2104_;
v___y_2078_ = v___x_2100_;
v___y_2079_ = v_a_2099_;
v___y_2080_ = v___x_2113_;
goto v___jp_2076_;
}
}
v___jp_2114_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2116_ = lean_array_to_list(v___y_2115_);
v___x_2117_ = lean_box(0);
v___x_2118_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_2039_, v___x_2116_, v___x_2117_, v___y_2043_, v___y_2044_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref_known(v___x_2118_, 1);
v___x_2120_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2121_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9);
v___x_2122_ = l_Lean_MessageData_joinSep(v_a_2119_, v___x_2121_);
v___x_2123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2120_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
v_a_2099_ = v___x_2123_;
goto v___jp_2098_;
}
else
{
lean_del_object(v___x_2074_);
lean_dec(v_snd_2072_);
lean_dec(v_fst_2071_);
lean_del_object(v___x_2069_);
lean_dec(v_fst_2067_);
lean_del_object(v___x_2051_);
lean_dec(v_tail_2049_);
lean_dec(v_x_2042_);
return v___x_2118_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_x_2149_, lean_object* v_x_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_2147_, v_a_2148_, v_x_2149_, v_x_2150_, v___y_2151_, v___y_2152_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v_a_2148_);
lean_dec(v_a_2147_);
return v_res_2154_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(uint8_t v_suppressElabErrors_2156_, uint8_t v___y_2157_, lean_object* v_x_2158_){
_start:
{
if (lean_obj_tag(v_x_2158_) == 1)
{
lean_object* v_pre_2159_; 
v_pre_2159_ = lean_ctor_get(v_x_2158_, 0);
if (lean_obj_tag(v_pre_2159_) == 0)
{
lean_object* v_str_2160_; lean_object* v___x_2161_; uint8_t v___x_2162_; 
v_str_2160_ = lean_ctor_get(v_x_2158_, 1);
v___x_2161_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0));
v___x_2162_ = lean_string_dec_eq(v_str_2160_, v___x_2161_);
if (v___x_2162_ == 0)
{
return v___x_2162_;
}
else
{
return v_suppressElabErrors_2156_;
}
}
else
{
return v___y_2157_;
}
}
else
{
return v___y_2157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed(lean_object* v_suppressElabErrors_2163_, lean_object* v___y_2164_, lean_object* v_x_2165_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2166_; uint8_t v___y_17873__boxed_2167_; uint8_t v_res_2168_; lean_object* v_r_2169_; 
v_suppressElabErrors_boxed_2166_ = lean_unbox(v_suppressElabErrors_2163_);
v___y_17873__boxed_2167_ = lean_unbox(v___y_2164_);
v_res_2168_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(v_suppressElabErrors_boxed_2166_, v___y_17873__boxed_2167_, v_x_2165_);
lean_dec(v_x_2165_);
v_r_2169_ = lean_box(v_res_2168_);
return v_r_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(lean_object* v_ref_2170_, lean_object* v_msgData_2171_, uint8_t v_severity_2172_, uint8_t v_isSilent_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; uint8_t v___y_2181_; lean_object* v___y_2182_; uint8_t v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; uint8_t v___y_2242_; uint8_t v___y_2243_; uint8_t v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; uint8_t v___y_2270_; lean_object* v___y_2271_; uint8_t v___y_2272_; uint8_t v___y_2273_; lean_object* v___y_2274_; uint8_t v___y_2278_; uint8_t v___y_2279_; uint8_t v___y_2280_; uint8_t v___x_2295_; uint8_t v___y_2297_; uint8_t v___y_2298_; uint8_t v___y_2299_; uint8_t v___y_2301_; uint8_t v___x_2313_; 
v___x_2295_ = 2;
v___x_2313_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2172_, v___x_2295_);
if (v___x_2313_ == 0)
{
v___y_2301_ = v___x_2313_;
goto v___jp_2300_;
}
else
{
uint8_t v___x_2314_; 
lean_inc_ref(v_msgData_2171_);
v___x_2314_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2171_);
v___y_2301_ = v___x_2314_;
goto v___jp_2300_;
}
v___jp_2177_:
{
lean_object* v___x_2186_; 
v___x_2186_ = l_Lean_Elab_Command_getScope___redArg(v___y_2185_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v___x_2188_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
lean_dec_ref_known(v___x_2186_, 1);
v___x_2188_ = l_Lean_Elab_Command_getScope___redArg(v___y_2185_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2224_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2191_ = v___x_2188_;
v_isShared_2192_ = v_isSharedCheck_2224_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2188_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2224_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; lean_object* v_currNamespace_2194_; lean_object* v_openDecls_2195_; lean_object* v_env_2196_; lean_object* v_messages_2197_; lean_object* v_scopes_2198_; lean_object* v_usedQuotCtxts_2199_; lean_object* v_nextMacroScope_2200_; lean_object* v_maxRecDepth_2201_; lean_object* v_ngen_2202_; lean_object* v_auxDeclNGen_2203_; lean_object* v_infoState_2204_; lean_object* v_traceState_2205_; lean_object* v_snapshotTasks_2206_; lean_object* v_prevLinterStates_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2223_; 
v___x_2193_ = lean_st_ref_take(v___y_2185_);
v_currNamespace_2194_ = lean_ctor_get(v_a_2187_, 2);
lean_inc(v_currNamespace_2194_);
lean_dec(v_a_2187_);
v_openDecls_2195_ = lean_ctor_get(v_a_2189_, 3);
lean_inc(v_openDecls_2195_);
lean_dec(v_a_2189_);
v_env_2196_ = lean_ctor_get(v___x_2193_, 0);
v_messages_2197_ = lean_ctor_get(v___x_2193_, 1);
v_scopes_2198_ = lean_ctor_get(v___x_2193_, 2);
v_usedQuotCtxts_2199_ = lean_ctor_get(v___x_2193_, 3);
v_nextMacroScope_2200_ = lean_ctor_get(v___x_2193_, 4);
v_maxRecDepth_2201_ = lean_ctor_get(v___x_2193_, 5);
v_ngen_2202_ = lean_ctor_get(v___x_2193_, 6);
v_auxDeclNGen_2203_ = lean_ctor_get(v___x_2193_, 7);
v_infoState_2204_ = lean_ctor_get(v___x_2193_, 8);
v_traceState_2205_ = lean_ctor_get(v___x_2193_, 9);
v_snapshotTasks_2206_ = lean_ctor_get(v___x_2193_, 10);
v_prevLinterStates_2207_ = lean_ctor_get(v___x_2193_, 11);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2209_ = v___x_2193_;
v_isShared_2210_ = v_isSharedCheck_2223_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_prevLinterStates_2207_);
lean_inc(v_snapshotTasks_2206_);
lean_inc(v_traceState_2205_);
lean_inc(v_infoState_2204_);
lean_inc(v_auxDeclNGen_2203_);
lean_inc(v_ngen_2202_);
lean_inc(v_maxRecDepth_2201_);
lean_inc(v_nextMacroScope_2200_);
lean_inc(v_usedQuotCtxts_2199_);
lean_inc(v_scopes_2198_);
lean_inc(v_messages_2197_);
lean_inc(v_env_2196_);
lean_dec(v___x_2193_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2223_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2216_; 
v___x_2211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2211_, 0, v_currNamespace_2194_);
lean_ctor_set(v___x_2211_, 1, v_openDecls_2195_);
v___x_2212_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
lean_ctor_set(v___x_2212_, 1, v___y_2182_);
lean_inc_ref(v___y_2180_);
lean_inc_ref(v___y_2179_);
v___x_2213_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2213_, 0, v___y_2179_);
lean_ctor_set(v___x_2213_, 1, v___y_2184_);
lean_ctor_set(v___x_2213_, 2, v___y_2178_);
lean_ctor_set(v___x_2213_, 3, v___y_2180_);
lean_ctor_set(v___x_2213_, 4, v___x_2212_);
lean_ctor_set_uint8(v___x_2213_, sizeof(void*)*5, v___y_2181_);
lean_ctor_set_uint8(v___x_2213_, sizeof(void*)*5 + 1, v___y_2183_);
lean_ctor_set_uint8(v___x_2213_, sizeof(void*)*5 + 2, v_isSilent_2173_);
v___x_2214_ = l_Lean_MessageLog_add(v___x_2213_, v_messages_2197_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 1, v___x_2214_);
v___x_2216_ = v___x_2209_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_env_2196_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v___x_2214_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v_scopes_2198_);
lean_ctor_set(v_reuseFailAlloc_2222_, 3, v_usedQuotCtxts_2199_);
lean_ctor_set(v_reuseFailAlloc_2222_, 4, v_nextMacroScope_2200_);
lean_ctor_set(v_reuseFailAlloc_2222_, 5, v_maxRecDepth_2201_);
lean_ctor_set(v_reuseFailAlloc_2222_, 6, v_ngen_2202_);
lean_ctor_set(v_reuseFailAlloc_2222_, 7, v_auxDeclNGen_2203_);
lean_ctor_set(v_reuseFailAlloc_2222_, 8, v_infoState_2204_);
lean_ctor_set(v_reuseFailAlloc_2222_, 9, v_traceState_2205_);
lean_ctor_set(v_reuseFailAlloc_2222_, 10, v_snapshotTasks_2206_);
lean_ctor_set(v_reuseFailAlloc_2222_, 11, v_prevLinterStates_2207_);
v___x_2216_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2217_ = lean_st_ref_put(v___y_2185_, v___x_2216_);
v___x_2218_ = lean_box(0);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 0, v___x_2218_);
v___x_2220_ = v___x_2191_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec(v_a_2187_);
lean_dec_ref(v___y_2184_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2178_);
v_a_2225_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2188_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2188_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec_ref(v___y_2184_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2178_);
v_a_2233_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2186_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2186_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
v___jp_2241_:
{
lean_object* v_fileName_2247_; lean_object* v_fileMap_2248_; uint8_t v_suppressElabErrors_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2268_; 
v_fileName_2247_ = lean_ctor_get(v___y_2174_, 0);
v_fileMap_2248_ = lean_ctor_get(v___y_2174_, 1);
v_suppressElabErrors_2249_ = lean_ctor_get_uint8(v___y_2174_, sizeof(void*)*10);
v___x_2250_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2171_);
v___x_2251_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v___x_2250_, v___y_2175_);
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2254_ = v___x_2251_;
v_isShared_2255_ = v_isSharedCheck_2268_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2251_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2268_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
lean_inc_ref_n(v_fileMap_2248_, 2);
v___x_2256_ = l_Lean_FileMap_toPosition(v_fileMap_2248_, v___y_2245_);
lean_dec(v___y_2245_);
v___x_2257_ = l_Lean_FileMap_toPosition(v_fileMap_2248_, v___y_2246_);
lean_dec(v___y_2246_);
v___x_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
v___x_2259_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
if (v_suppressElabErrors_2249_ == 0)
{
lean_del_object(v___x_2254_);
v___y_2178_ = v___x_2258_;
v___y_2179_ = v_fileName_2247_;
v___y_2180_ = v___x_2259_;
v___y_2181_ = v___y_2243_;
v___y_2182_ = v_a_2252_;
v___y_2183_ = v___y_2244_;
v___y_2184_ = v___x_2256_;
v___y_2185_ = v___y_2175_;
goto v___jp_2177_;
}
else
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___f_2262_; uint8_t v___x_2263_; 
v___x_2260_ = lean_box(v_suppressElabErrors_2249_);
v___x_2261_ = lean_box(v___y_2242_);
v___f_2262_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2262_, 0, v___x_2260_);
lean_closure_set(v___f_2262_, 1, v___x_2261_);
lean_inc(v_a_2252_);
v___x_2263_ = l_Lean_MessageData_hasTag(v___f_2262_, v_a_2252_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; lean_object* v___x_2266_; 
lean_dec_ref_known(v___x_2258_, 1);
lean_dec_ref(v___x_2256_);
lean_dec(v_a_2252_);
v___x_2264_ = lean_box(0);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v___x_2264_);
v___x_2266_ = v___x_2254_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2264_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
else
{
lean_del_object(v___x_2254_);
v___y_2178_ = v___x_2258_;
v___y_2179_ = v_fileName_2247_;
v___y_2180_ = v___x_2259_;
v___y_2181_ = v___y_2243_;
v___y_2182_ = v_a_2252_;
v___y_2183_ = v___y_2244_;
v___y_2184_ = v___x_2256_;
v___y_2185_ = v___y_2175_;
goto v___jp_2177_;
}
}
}
}
v___jp_2269_:
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_Syntax_getTailPos_x3f(v___y_2271_, v___y_2272_);
lean_dec(v___y_2271_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_inc(v___y_2274_);
v___y_2242_ = v___y_2270_;
v___y_2243_ = v___y_2272_;
v___y_2244_ = v___y_2273_;
v___y_2245_ = v___y_2274_;
v___y_2246_ = v___y_2274_;
goto v___jp_2241_;
}
else
{
lean_object* v_val_2276_; 
v_val_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_val_2276_);
lean_dec_ref_known(v___x_2275_, 1);
v___y_2242_ = v___y_2270_;
v___y_2243_ = v___y_2272_;
v___y_2244_ = v___y_2273_;
v___y_2245_ = v___y_2274_;
v___y_2246_ = v_val_2276_;
goto v___jp_2241_;
}
}
v___jp_2277_:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_Elab_Command_getRef___redArg(v___y_2174_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v_ref_2283_; lean_object* v___x_2284_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v___x_2281_, 1);
v_ref_2283_ = l_Lean_replaceRef(v_ref_2170_, v_a_2282_);
lean_dec(v_a_2282_);
v___x_2284_ = l_Lean_Syntax_getPos_x3f(v_ref_2283_, v___y_2279_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v___x_2285_; 
v___x_2285_ = lean_unsigned_to_nat(0u);
v___y_2270_ = v___y_2278_;
v___y_2271_ = v_ref_2283_;
v___y_2272_ = v___y_2279_;
v___y_2273_ = v___y_2280_;
v___y_2274_ = v___x_2285_;
goto v___jp_2269_;
}
else
{
lean_object* v_val_2286_; 
v_val_2286_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_val_2286_);
lean_dec_ref_known(v___x_2284_, 1);
v___y_2270_ = v___y_2278_;
v___y_2271_ = v_ref_2283_;
v___y_2272_ = v___y_2279_;
v___y_2273_ = v___y_2280_;
v___y_2274_ = v_val_2286_;
goto v___jp_2269_;
}
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec_ref(v_msgData_2171_);
v_a_2287_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2281_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2281_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
v___jp_2296_:
{
if (v___y_2299_ == 0)
{
v___y_2278_ = v___y_2297_;
v___y_2279_ = v___y_2298_;
v___y_2280_ = v_severity_2172_;
goto v___jp_2277_;
}
else
{
v___y_2278_ = v___y_2297_;
v___y_2279_ = v___y_2298_;
v___y_2280_ = v___x_2295_;
goto v___jp_2277_;
}
}
v___jp_2300_:
{
if (v___y_2301_ == 0)
{
lean_object* v___x_2302_; lean_object* v_scopes_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v_opts_2306_; uint8_t v___x_2307_; uint8_t v___x_2308_; 
v___x_2302_ = lean_st_ref_get(v___y_2175_);
v_scopes_2303_ = lean_ctor_get(v___x_2302_, 2);
lean_inc(v_scopes_2303_);
lean_dec(v___x_2302_);
v___x_2304_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2305_ = l_List_head_x21___redArg(v___x_2304_, v_scopes_2303_);
lean_dec(v_scopes_2303_);
v_opts_2306_ = lean_ctor_get(v___x_2305_, 1);
lean_inc_ref(v_opts_2306_);
lean_dec(v___x_2305_);
v___x_2307_ = 1;
v___x_2308_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2172_, v___x_2307_);
if (v___x_2308_ == 0)
{
lean_dec_ref(v_opts_2306_);
v___y_2297_ = v___y_2301_;
v___y_2298_ = v___y_2301_;
v___y_2299_ = v___x_2308_;
goto v___jp_2296_;
}
else
{
lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2309_ = l_Lean_warningAsError;
v___x_2310_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_2306_, v___x_2309_);
lean_dec_ref(v_opts_2306_);
v___y_2297_ = v___y_2301_;
v___y_2298_ = v___y_2301_;
v___y_2299_ = v___x_2310_;
goto v___jp_2296_;
}
}
else
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
lean_dec_ref(v_msgData_2171_);
v___x_2311_ = lean_box(0);
v___x_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
return v___x_2312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___boxed(lean_object* v_ref_2315_, lean_object* v_msgData_2316_, lean_object* v_severity_2317_, lean_object* v_isSilent_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
uint8_t v_severity_boxed_2322_; uint8_t v_isSilent_boxed_2323_; lean_object* v_res_2324_; 
v_severity_boxed_2322_ = lean_unbox(v_severity_2317_);
v_isSilent_boxed_2323_ = lean_unbox(v_isSilent_2318_);
v_res_2324_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_ref_2315_, v_msgData_2316_, v_severity_boxed_2322_, v_isSilent_boxed_2323_, v___y_2319_, v___y_2320_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v_ref_2315_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(lean_object* v_msgData_2325_, uint8_t v_severity_2326_, uint8_t v_isSilent_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Lean_Elab_Command_getRef___redArg(v___y_2328_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2333_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2331_, 1);
v___x_2333_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_a_2332_, v_msgData_2325_, v_severity_2326_, v_isSilent_2327_, v___y_2328_, v___y_2329_);
lean_dec(v_a_2332_);
return v___x_2333_;
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec_ref(v_msgData_2325_);
v_a_2334_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2331_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2331_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26___boxed(lean_object* v_msgData_2342_, lean_object* v_severity_2343_, lean_object* v_isSilent_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
uint8_t v_severity_boxed_2348_; uint8_t v_isSilent_boxed_2349_; lean_object* v_res_2350_; 
v_severity_boxed_2348_ = lean_unbox(v_severity_2343_);
v_isSilent_boxed_2349_ = lean_unbox(v_isSilent_2344_);
v_res_2350_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_2342_, v_severity_boxed_2348_, v_isSilent_boxed_2349_, v___y_2345_, v___y_2346_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object* v_msgData_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
uint8_t v___x_2355_; uint8_t v___x_2356_; lean_object* v___x_2357_; 
v___x_2355_ = 0;
v___x_2356_ = 0;
v___x_2357_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_2351_, v___x_2355_, v___x_2356_, v___y_2352_, v___y_2353_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object* v_msgData_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v_msgData_2358_, v___y_2359_, v___y_2360_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object* v_init_2363_, lean_object* v_x_2364_){
_start:
{
if (lean_obj_tag(v_x_2364_) == 0)
{
lean_object* v_k_2366_; lean_object* v_v_2367_; lean_object* v_l_2368_; lean_object* v_r_2369_; lean_object* v___x_2370_; lean_object* v_a_2371_; lean_object* v_a_2372_; lean_object* v___x_2373_; 
v_k_2366_ = lean_ctor_get(v_x_2364_, 1);
lean_inc(v_k_2366_);
v_v_2367_ = lean_ctor_get(v_x_2364_, 2);
lean_inc(v_v_2367_);
v_l_2368_ = lean_ctor_get(v_x_2364_, 3);
lean_inc(v_l_2368_);
v_r_2369_ = lean_ctor_get(v_x_2364_, 4);
lean_inc(v_r_2369_);
lean_dec_ref_known(v_x_2364_, 5);
v___x_2370_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_2363_, v_l_2368_);
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_a_2371_);
lean_dec_ref(v___x_2370_);
v_a_2372_ = lean_ctor_get(v_a_2371_, 0);
lean_inc(v_a_2372_);
lean_dec(v_a_2371_);
v___x_2373_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2366_, v_v_2367_, v_a_2372_);
v_init_2363_ = v___x_2373_;
v_x_2364_ = v_r_2369_;
goto _start;
}
else
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2375_, 0, v_init_2363_);
v___x_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
return v___x_2376_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object* v_init_2377_, lean_object* v_x_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_2377_, v_x_2378_);
return v_res_2380_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(uint8_t v___x_2381_, lean_object* v_x1_2382_, lean_object* v_x2_2383_){
_start:
{
lean_object* v_fst_2384_; lean_object* v_fst_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; uint8_t v___x_2388_; 
v_fst_2384_ = lean_ctor_get(v_x1_2382_, 0);
lean_inc(v_fst_2384_);
lean_dec_ref(v_x1_2382_);
v_fst_2385_ = lean_ctor_get(v_x2_2383_, 0);
lean_inc(v_fst_2385_);
lean_dec_ref(v_x2_2383_);
v___x_2386_ = l_Lean_Name_toString(v_fst_2384_, v___x_2381_);
v___x_2387_ = l_Lean_Name_toString(v_fst_2385_, v___x_2381_);
v___x_2388_ = lean_string_dec_lt(v___x_2386_, v___x_2387_);
lean_dec_ref(v___x_2387_);
lean_dec_ref(v___x_2386_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0___boxed(lean_object* v___x_2389_, lean_object* v_x1_2390_, lean_object* v_x2_2391_){
_start:
{
uint8_t v___x_18216__boxed_2392_; uint8_t v_res_2393_; lean_object* v_r_2394_; 
v___x_18216__boxed_2392_ = lean_unbox(v___x_2389_);
v_res_2393_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_18216__boxed_2392_, v_x1_2390_, v_x2_2391_);
v_r_2394_ = lean_box(v_res_2393_);
return v_r_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(lean_object* v_hi_2395_, lean_object* v_pivot_2396_, lean_object* v_as_2397_, lean_object* v_i_2398_, lean_object* v_k_2399_){
_start:
{
uint8_t v___x_2400_; 
v___x_2400_ = lean_nat_dec_lt(v_k_2399_, v_hi_2395_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
lean_dec(v_k_2399_);
lean_dec_ref(v_pivot_2396_);
v___x_2401_ = lean_array_fswap(v_as_2397_, v_i_2398_, v_hi_2395_);
v___x_2402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2402_, 0, v_i_2398_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
return v___x_2402_;
}
else
{
lean_object* v___x_2403_; lean_object* v_fst_2404_; lean_object* v_fst_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; uint8_t v___x_2408_; 
v___x_2403_ = lean_array_fget_borrowed(v_as_2397_, v_k_2399_);
v_fst_2404_ = lean_ctor_get(v___x_2403_, 0);
v_fst_2405_ = lean_ctor_get(v_pivot_2396_, 0);
lean_inc(v_fst_2404_);
v___x_2406_ = l_Lean_Name_toString(v_fst_2404_, v___x_2400_);
lean_inc(v_fst_2405_);
v___x_2407_ = l_Lean_Name_toString(v_fst_2405_, v___x_2400_);
v___x_2408_ = lean_string_dec_lt(v___x_2406_, v___x_2407_);
lean_dec_ref(v___x_2407_);
lean_dec_ref(v___x_2406_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2409_ = lean_unsigned_to_nat(1u);
v___x_2410_ = lean_nat_add(v_k_2399_, v___x_2409_);
lean_dec(v_k_2399_);
v_k_2399_ = v___x_2410_;
goto _start;
}
else
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2412_ = lean_array_fswap(v_as_2397_, v_i_2398_, v_k_2399_);
v___x_2413_ = lean_unsigned_to_nat(1u);
v___x_2414_ = lean_nat_add(v_i_2398_, v___x_2413_);
lean_dec(v_i_2398_);
v___x_2415_ = lean_nat_add(v_k_2399_, v___x_2413_);
lean_dec(v_k_2399_);
v_as_2397_ = v___x_2412_;
v_i_2398_ = v___x_2414_;
v_k_2399_ = v___x_2415_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg___boxed(lean_object* v_hi_2417_, lean_object* v_pivot_2418_, lean_object* v_as_2419_, lean_object* v_i_2420_, lean_object* v_k_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_2417_, v_pivot_2418_, v_as_2419_, v_i_2420_, v_k_2421_);
lean_dec(v_hi_2417_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(lean_object* v_n_2423_, lean_object* v_as_2424_, lean_object* v_lo_2425_, lean_object* v_hi_2426_){
_start:
{
lean_object* v___y_2428_; uint8_t v___x_2438_; 
v___x_2438_ = lean_nat_dec_lt(v_lo_2425_, v_hi_2426_);
if (v___x_2438_ == 0)
{
lean_dec(v_lo_2425_);
return v_as_2424_;
}
else
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v_mid_2441_; lean_object* v___y_2443_; lean_object* v___y_2449_; lean_object* v___x_2454_; lean_object* v___x_2455_; uint8_t v___x_2456_; 
v___x_2439_ = lean_nat_add(v_lo_2425_, v_hi_2426_);
v___x_2440_ = lean_unsigned_to_nat(1u);
v_mid_2441_ = lean_nat_shiftr(v___x_2439_, v___x_2440_);
lean_dec(v___x_2439_);
v___x_2454_ = lean_array_fget_borrowed(v_as_2424_, v_mid_2441_);
v___x_2455_ = lean_array_fget_borrowed(v_as_2424_, v_lo_2425_);
lean_inc(v___x_2455_);
lean_inc(v___x_2454_);
v___x_2456_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2438_, v___x_2454_, v___x_2455_);
if (v___x_2456_ == 0)
{
v___y_2449_ = v_as_2424_;
goto v___jp_2448_;
}
else
{
lean_object* v___x_2457_; 
v___x_2457_ = lean_array_fswap(v_as_2424_, v_lo_2425_, v_mid_2441_);
v___y_2449_ = v___x_2457_;
goto v___jp_2448_;
}
v___jp_2442_:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; uint8_t v___x_2446_; 
v___x_2444_ = lean_array_fget_borrowed(v___y_2443_, v_mid_2441_);
v___x_2445_ = lean_array_fget_borrowed(v___y_2443_, v_hi_2426_);
lean_inc(v___x_2445_);
lean_inc(v___x_2444_);
v___x_2446_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2438_, v___x_2444_, v___x_2445_);
if (v___x_2446_ == 0)
{
lean_dec(v_mid_2441_);
v___y_2428_ = v___y_2443_;
goto v___jp_2427_;
}
else
{
lean_object* v___x_2447_; 
v___x_2447_ = lean_array_fswap(v___y_2443_, v_mid_2441_, v_hi_2426_);
lean_dec(v_mid_2441_);
v___y_2428_ = v___x_2447_;
goto v___jp_2427_;
}
}
v___jp_2448_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; uint8_t v___x_2452_; 
v___x_2450_ = lean_array_fget_borrowed(v___y_2449_, v_hi_2426_);
v___x_2451_ = lean_array_fget_borrowed(v___y_2449_, v_lo_2425_);
lean_inc(v___x_2451_);
lean_inc(v___x_2450_);
v___x_2452_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2438_, v___x_2450_, v___x_2451_);
if (v___x_2452_ == 0)
{
v___y_2443_ = v___y_2449_;
goto v___jp_2442_;
}
else
{
lean_object* v___x_2453_; 
v___x_2453_ = lean_array_fswap(v___y_2449_, v_lo_2425_, v_hi_2426_);
v___y_2443_ = v___x_2453_;
goto v___jp_2442_;
}
}
}
v___jp_2427_:
{
lean_object* v_pivot_2429_; lean_object* v___x_2430_; lean_object* v_fst_2431_; lean_object* v_snd_2432_; uint8_t v___x_2433_; 
v_pivot_2429_ = lean_array_fget(v___y_2428_, v_hi_2426_);
lean_inc_n(v_lo_2425_, 2);
v___x_2430_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_2426_, v_pivot_2429_, v___y_2428_, v_lo_2425_, v_lo_2425_);
v_fst_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_fst_2431_);
v_snd_2432_ = lean_ctor_get(v___x_2430_, 1);
lean_inc(v_snd_2432_);
lean_dec_ref(v___x_2430_);
v___x_2433_ = lean_nat_dec_le(v_hi_2426_, v_fst_2431_);
if (v___x_2433_ == 0)
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2434_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_2423_, v_snd_2432_, v_lo_2425_, v_fst_2431_);
v___x_2435_ = lean_unsigned_to_nat(1u);
v___x_2436_ = lean_nat_add(v_fst_2431_, v___x_2435_);
lean_dec(v_fst_2431_);
v_as_2424_ = v___x_2434_;
v_lo_2425_ = v___x_2436_;
goto _start;
}
else
{
lean_dec(v_fst_2431_);
lean_dec(v_lo_2425_);
return v_snd_2432_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___boxed(lean_object* v_n_2458_, lean_object* v_as_2459_, lean_object* v_lo_2460_, lean_object* v_hi_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_2458_, v_as_2459_, v_lo_2460_, v_hi_2461_);
lean_dec(v_hi_2461_);
lean_dec(v_n_2458_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(lean_object* v_init_2463_, lean_object* v_x_2464_){
_start:
{
if (lean_obj_tag(v_x_2464_) == 0)
{
lean_object* v_k_2465_; lean_object* v_v_2466_; lean_object* v_l_2467_; lean_object* v_r_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v_k_2465_ = lean_ctor_get(v_x_2464_, 1);
v_v_2466_ = lean_ctor_get(v_x_2464_, 2);
v_l_2467_ = lean_ctor_get(v_x_2464_, 3);
v_r_2468_ = lean_ctor_get(v_x_2464_, 4);
v___x_2469_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_2463_, v_l_2467_);
lean_inc(v_v_2466_);
lean_inc(v_k_2465_);
v___x_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2470_, 0, v_k_2465_);
lean_ctor_set(v___x_2470_, 1, v_v_2466_);
v___x_2471_ = lean_array_push(v___x_2469_, v___x_2470_);
v_init_2463_ = v___x_2471_;
v_x_2464_ = v_r_2468_;
goto _start;
}
else
{
return v_init_2463_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25___boxed(lean_object* v_init_2473_, lean_object* v_x_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_2473_, v_x_2474_);
lean_dec(v_x_2474_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(lean_object* v_as_2476_, size_t v_sz_2477_, size_t v_i_2478_, lean_object* v_b_2479_){
_start:
{
uint8_t v___x_2481_; 
v___x_2481_ = lean_usize_dec_lt(v_i_2478_, v_sz_2477_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; 
v___x_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2482_, 0, v_b_2479_);
return v___x_2482_;
}
else
{
lean_object* v_a_2483_; lean_object* v_fst_2484_; lean_object* v_snd_2485_; lean_object* v_found_2486_; size_t v___x_2487_; size_t v___x_2488_; 
v_a_2483_ = lean_array_uget_borrowed(v_as_2476_, v_i_2478_);
v_fst_2484_ = lean_ctor_get(v_a_2483_, 0);
v_snd_2485_ = lean_ctor_get(v_a_2483_, 1);
lean_inc(v_snd_2485_);
lean_inc(v_fst_2484_);
v_found_2486_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2484_, v_snd_2485_, v_b_2479_);
v___x_2487_ = ((size_t)1ULL);
v___x_2488_ = lean_usize_add(v_i_2478_, v___x_2487_);
v_i_2478_ = v___x_2488_;
v_b_2479_ = v_found_2486_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg___boxed(lean_object* v_as_2490_, lean_object* v_sz_2491_, lean_object* v_i_2492_, lean_object* v_b_2493_, lean_object* v___y_2494_){
_start:
{
size_t v_sz_boxed_2495_; size_t v_i_boxed_2496_; lean_object* v_res_2497_; 
v_sz_boxed_2495_ = lean_unbox_usize(v_sz_2491_);
lean_dec(v_sz_2491_);
v_i_boxed_2496_ = lean_unbox_usize(v_i_2492_);
lean_dec(v_i_2492_);
v_res_2497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_2490_, v_sz_boxed_2495_, v_i_boxed_2496_, v_b_2493_);
lean_dec_ref(v_as_2490_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object* v_as_2498_, size_t v_sz_2499_, size_t v_i_2500_, lean_object* v_b_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
uint8_t v___x_2505_; 
v___x_2505_ = lean_usize_dec_lt(v_i_2500_, v_sz_2499_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2506_; 
v___x_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2506_, 0, v_b_2501_);
return v___x_2506_;
}
else
{
lean_object* v_a_2507_; size_t v_sz_2508_; size_t v___x_2509_; lean_object* v___x_2510_; 
v_a_2507_ = lean_array_uget_borrowed(v_as_2498_, v_i_2500_);
v_sz_2508_ = lean_array_size(v_a_2507_);
v___x_2509_ = ((size_t)0ULL);
v___x_2510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_a_2507_, v_sz_2508_, v___x_2509_, v_b_2501_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v_a_2511_; size_t v___x_2512_; size_t v___x_2513_; 
v_a_2511_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_a_2511_);
lean_dec_ref_known(v___x_2510_, 1);
v___x_2512_ = ((size_t)1ULL);
v___x_2513_ = lean_usize_add(v_i_2500_, v___x_2512_);
v_i_2500_ = v___x_2513_;
v_b_2501_ = v_a_2511_;
goto _start;
}
else
{
return v___x_2510_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object* v_as_2515_, lean_object* v_sz_2516_, lean_object* v_i_2517_, lean_object* v_b_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
size_t v_sz_boxed_2522_; size_t v_i_boxed_2523_; lean_object* v_res_2524_; 
v_sz_boxed_2522_ = lean_unbox_usize(v_sz_2516_);
lean_dec(v_sz_2516_);
v_i_boxed_2523_ = lean_unbox_usize(v_i_2517_);
lean_dec(v_i_2517_);
v_res_2524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_as_2515_, v_sz_boxed_2522_, v_i_boxed_2523_, v_b_2518_, v___y_2519_, v___y_2520_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec_ref(v_as_2515_);
return v_res_2524_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = lean_box(1);
v___x_2526_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2525_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v___y_2533_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___x_2548_; lean_object* v_env_2549_; lean_object* v___x_2550_; lean_object* v_toEnvExtension_2551_; lean_object* v_asyncMode_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v_a_2558_; lean_object* v_a_2560_; lean_object* v_a_2583_; 
v___x_2548_ = lean_st_ref_get(v___y_2530_);
v_env_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc_ref_n(v_env_2549_, 2);
lean_dec(v___x_2548_);
v___x_2550_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2551_ = lean_ctor_get(v___x_2550_, 0);
v_asyncMode_2552_ = lean_ctor_get(v_toEnvExtension_2551_, 2);
v___x_2553_ = lean_box(1);
v___x_2554_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0, &l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0);
v___x_2555_ = lean_box(0);
v___x_2556_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2553_, v___x_2550_, v_env_2549_, v_asyncMode_2552_, v___x_2555_);
v___x_2557_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v___x_2553_, v___x_2556_);
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_a_2558_);
lean_dec_ref(v___x_2557_);
v_a_2583_ = lean_ctor_get(v_a_2558_, 0);
lean_inc(v_a_2583_);
lean_dec(v_a_2558_);
v_a_2560_ = v_a_2583_;
goto v___jp_2559_;
v___jp_2532_:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2534_ = lean_array_to_list(v___y_2533_);
v___x_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2534_);
return v___x_2535_;
}
v___jp_2536_:
{
lean_object* v___x_2541_; 
v___x_2541_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v___y_2539_, v___y_2537_, v___y_2538_, v___y_2540_);
lean_dec(v___y_2540_);
lean_dec(v___y_2539_);
v___y_2533_ = v___x_2541_;
goto v___jp_2532_;
}
v___jp_2542_:
{
uint8_t v___x_2547_; 
v___x_2547_ = lean_nat_dec_le(v___y_2546_, v___y_2543_);
if (v___x_2547_ == 0)
{
lean_dec(v___y_2543_);
lean_inc(v___y_2546_);
v___y_2537_ = v___y_2544_;
v___y_2538_ = v___y_2546_;
v___y_2539_ = v___y_2545_;
v___y_2540_ = v___y_2546_;
goto v___jp_2536_;
}
else
{
v___y_2537_ = v___y_2544_;
v___y_2538_ = v___y_2546_;
v___y_2539_ = v___y_2545_;
v___y_2540_ = v___y_2543_;
goto v___jp_2536_;
}
}
v___jp_2559_:
{
lean_object* v___x_2561_; lean_object* v_importedEntries_2562_; size_t v_sz_2563_; size_t v___x_2564_; lean_object* v___x_2565_; 
v___x_2561_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2554_, v_toEnvExtension_2551_, v_env_2549_, v_asyncMode_2552_, v___x_2555_);
v_importedEntries_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc_ref(v_importedEntries_2562_);
lean_dec(v___x_2561_);
v_sz_2563_ = lean_array_size(v_importedEntries_2562_);
v___x_2564_ = ((size_t)0ULL);
v___x_2565_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_importedEntries_2562_, v_sz_2563_, v___x_2564_, v_a_2560_, v___y_2529_, v___y_2530_);
lean_dec_ref(v_importedEntries_2562_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v_arr_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2565_, 1);
v___x_2567_ = lean_unsigned_to_nat(0u);
v___x_2568_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1));
v_arr_2569_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v___x_2568_, v_a_2566_);
lean_dec(v_a_2566_);
v___x_2570_ = lean_array_get_size(v_arr_2569_);
v___x_2571_ = lean_nat_dec_eq(v___x_2570_, v___x_2567_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; lean_object* v___x_2573_; uint8_t v___x_2574_; 
v___x_2572_ = lean_unsigned_to_nat(1u);
v___x_2573_ = lean_nat_sub(v___x_2570_, v___x_2572_);
v___x_2574_ = lean_nat_dec_le(v___x_2567_, v___x_2573_);
if (v___x_2574_ == 0)
{
lean_inc(v___x_2573_);
v___y_2543_ = v___x_2573_;
v___y_2544_ = v_arr_2569_;
v___y_2545_ = v___x_2570_;
v___y_2546_ = v___x_2573_;
goto v___jp_2542_;
}
else
{
v___y_2543_ = v___x_2573_;
v___y_2544_ = v_arr_2569_;
v___y_2545_ = v___x_2570_;
v___y_2546_ = v___x_2567_;
goto v___jp_2542_;
}
}
else
{
v___y_2533_ = v_arr_2569_;
goto v___jp_2532_;
}
}
else
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
v_a_2575_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2577_ = v___x_2565_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2565_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2575_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v___y_2584_, v___y_2585_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object* v_t_2588_, lean_object* v_k_2589_, lean_object* v_fallback_2590_){
_start:
{
if (lean_obj_tag(v_t_2588_) == 0)
{
lean_object* v_k_2591_; lean_object* v_v_2592_; lean_object* v_l_2593_; lean_object* v_r_2594_; uint8_t v___x_2595_; 
v_k_2591_ = lean_ctor_get(v_t_2588_, 1);
v_v_2592_ = lean_ctor_get(v_t_2588_, 2);
v_l_2593_ = lean_ctor_get(v_t_2588_, 3);
v_r_2594_ = lean_ctor_get(v_t_2588_, 4);
v___x_2595_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2589_, v_k_2591_);
switch(v___x_2595_)
{
case 0:
{
v_t_2588_ = v_l_2593_;
goto _start;
}
case 1:
{
lean_inc(v_v_2592_);
return v_v_2592_;
}
default: 
{
v_t_2588_ = v_r_2594_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2590_);
return v_fallback_2590_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object* v_t_2598_, lean_object* v_k_2599_, lean_object* v_fallback_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_2598_, v_k_2599_, v_fallback_2600_);
lean_dec(v_fallback_2600_);
lean_dec(v_k_2599_);
lean_dec(v_t_2598_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object* v_as_2602_, size_t v_sz_2603_, size_t v_i_2604_, lean_object* v_b_2605_){
_start:
{
uint8_t v___x_2607_; 
v___x_2607_ = lean_usize_dec_lt(v_i_2604_, v_sz_2603_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2608_; 
v___x_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2608_, 0, v_b_2605_);
return v___x_2608_;
}
else
{
lean_object* v_a_2609_; lean_object* v_fst_2610_; lean_object* v_snd_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; size_t v___x_2616_; size_t v___x_2617_; 
v_a_2609_ = lean_array_uget_borrowed(v_as_2602_, v_i_2604_);
v_fst_2610_ = lean_ctor_get(v_a_2609_, 0);
v_snd_2611_ = lean_ctor_get(v_a_2609_, 1);
v___x_2612_ = l_Lean_NameSet_empty;
v___x_2613_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_2605_, v_snd_2611_, v___x_2612_);
lean_inc(v_fst_2610_);
v___x_2614_ = l_Lean_NameSet_insert(v___x_2613_, v_fst_2610_);
lean_inc(v_snd_2611_);
v___x_2615_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_snd_2611_, v___x_2614_, v_b_2605_);
v___x_2616_ = ((size_t)1ULL);
v___x_2617_ = lean_usize_add(v_i_2604_, v___x_2616_);
v_i_2604_ = v___x_2617_;
v_b_2605_ = v___x_2615_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object* v_as_2619_, lean_object* v_sz_2620_, lean_object* v_i_2621_, lean_object* v_b_2622_, lean_object* v___y_2623_){
_start:
{
size_t v_sz_boxed_2624_; size_t v_i_boxed_2625_; lean_object* v_res_2626_; 
v_sz_boxed_2624_ = lean_unbox_usize(v_sz_2620_);
lean_dec(v_sz_2620_);
v_i_boxed_2625_ = lean_unbox_usize(v_i_2621_);
lean_dec(v_i_2621_);
v_res_2626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_2619_, v_sz_boxed_2624_, v_i_boxed_2625_, v_b_2622_);
lean_dec_ref(v_as_2619_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object* v_as_2627_, size_t v_sz_2628_, size_t v_i_2629_, lean_object* v_b_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
uint8_t v___x_2634_; 
v___x_2634_ = lean_usize_dec_lt(v_i_2629_, v_sz_2628_);
if (v___x_2634_ == 0)
{
lean_object* v___x_2635_; 
v___x_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2635_, 0, v_b_2630_);
return v___x_2635_;
}
else
{
lean_object* v_a_2636_; size_t v_sz_2637_; size_t v___x_2638_; lean_object* v___x_2639_; 
v_a_2636_ = lean_array_uget_borrowed(v_as_2627_, v_i_2629_);
v_sz_2637_ = lean_array_size(v_a_2636_);
v___x_2638_ = ((size_t)0ULL);
v___x_2639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_a_2636_, v_sz_2637_, v___x_2638_, v_b_2630_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; size_t v___x_2641_; size_t v___x_2642_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_a_2640_);
lean_dec_ref_known(v___x_2639_, 1);
v___x_2641_ = ((size_t)1ULL);
v___x_2642_ = lean_usize_add(v_i_2629_, v___x_2641_);
v_i_2629_ = v___x_2642_;
v_b_2630_ = v_a_2640_;
goto _start;
}
else
{
return v___x_2639_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object* v_as_2644_, lean_object* v_sz_2645_, lean_object* v_i_2646_, lean_object* v_b_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
size_t v_sz_boxed_2651_; size_t v_i_boxed_2652_; lean_object* v_res_2653_; 
v_sz_boxed_2651_ = lean_unbox_usize(v_sz_2645_);
lean_dec(v_sz_2645_);
v_i_boxed_2652_ = lean_unbox_usize(v_i_2646_);
lean_dec(v_i_2646_);
v_res_2653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v_as_2644_, v_sz_boxed_2651_, v_i_boxed_2652_, v_b_2647_, v___y_2648_, v___y_2649_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec_ref(v_as_2644_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object* v_as_2654_, size_t v_i_2655_, size_t v_stop_2656_, lean_object* v_b_2657_){
_start:
{
uint8_t v___x_2658_; 
v___x_2658_ = lean_usize_dec_eq(v_i_2655_, v_stop_2656_);
if (v___x_2658_ == 0)
{
lean_object* v___x_2659_; lean_object* v_fst_2660_; lean_object* v_snd_2661_; lean_object* v___x_2662_; size_t v___x_2663_; size_t v___x_2664_; 
v___x_2659_ = lean_array_uget_borrowed(v_as_2654_, v_i_2655_);
v_fst_2660_ = lean_ctor_get(v___x_2659_, 0);
v_snd_2661_ = lean_ctor_get(v___x_2659_, 1);
lean_inc(v_snd_2661_);
lean_inc(v_fst_2660_);
v___x_2662_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2660_, v_snd_2661_, v_b_2657_);
v___x_2663_ = ((size_t)1ULL);
v___x_2664_ = lean_usize_add(v_i_2655_, v___x_2663_);
v_i_2655_ = v___x_2664_;
v_b_2657_ = v___x_2662_;
goto _start;
}
else
{
return v_b_2657_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object* v_as_2666_, lean_object* v_i_2667_, lean_object* v_stop_2668_, lean_object* v_b_2669_){
_start:
{
size_t v_i_boxed_2670_; size_t v_stop_boxed_2671_; lean_object* v_res_2672_; 
v_i_boxed_2670_ = lean_unbox_usize(v_i_2667_);
lean_dec(v_i_2667_);
v_stop_boxed_2671_ = lean_unbox_usize(v_stop_2668_);
lean_dec(v_stop_2668_);
v_res_2672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v_as_2666_, v_i_boxed_2670_, v_stop_boxed_2671_, v_b_2669_);
lean_dec_ref(v_as_2666_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object* v_as_2673_, size_t v_i_2674_, size_t v_stop_2675_, lean_object* v_b_2676_){
_start:
{
lean_object* v___y_2678_; uint8_t v___x_2682_; 
v___x_2682_ = lean_usize_dec_eq(v_i_2674_, v_stop_2675_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; uint8_t v___x_2686_; 
v___x_2683_ = lean_array_uget_borrowed(v_as_2673_, v_i_2674_);
v___x_2684_ = lean_unsigned_to_nat(0u);
v___x_2685_ = lean_array_get_size(v___x_2683_);
v___x_2686_ = lean_nat_dec_lt(v___x_2684_, v___x_2685_);
if (v___x_2686_ == 0)
{
v___y_2678_ = v_b_2676_;
goto v___jp_2677_;
}
else
{
size_t v___x_2687_; size_t v___x_2688_; lean_object* v___x_2689_; 
v___x_2687_ = ((size_t)0ULL);
v___x_2688_ = lean_usize_of_nat(v___x_2685_);
v___x_2689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_2683_, v___x_2687_, v___x_2688_, v_b_2676_);
v___y_2678_ = v___x_2689_;
goto v___jp_2677_;
}
}
else
{
return v_b_2676_;
}
v___jp_2677_:
{
size_t v___x_2679_; size_t v___x_2680_; 
v___x_2679_ = ((size_t)1ULL);
v___x_2680_ = lean_usize_add(v_i_2674_, v___x_2679_);
v_i_2674_ = v___x_2680_;
v_b_2676_ = v___y_2678_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object* v_as_2690_, lean_object* v_i_2691_, lean_object* v_stop_2692_, lean_object* v_b_2693_){
_start:
{
size_t v_i_boxed_2694_; size_t v_stop_boxed_2695_; lean_object* v_res_2696_; 
v_i_boxed_2694_ = lean_unbox_usize(v_i_2691_);
lean_dec(v_i_2691_);
v_stop_boxed_2695_ = lean_unbox_usize(v_stop_2692_);
lean_dec(v_stop_2692_);
v_res_2696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v_as_2690_, v_i_boxed_2694_, v_stop_boxed_2695_, v_b_2693_);
lean_dec_ref(v_as_2690_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object* v___y_2697_){
_start:
{
lean_object* v___x_2699_; lean_object* v_env_2700_; lean_object* v___x_2701_; lean_object* v_ext_2702_; lean_object* v_toEnvExtension_2703_; lean_object* v_asyncMode_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v_categories_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2699_ = lean_st_ref_get(v___y_2697_);
v_env_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc_ref_n(v_env_2700_, 2);
lean_dec(v___x_2699_);
v___x_2701_ = l_Lean_Parser_parserExtension;
v_ext_2702_ = lean_ctor_get(v___x_2701_, 1);
v_toEnvExtension_2703_ = lean_ctor_get(v_ext_2702_, 0);
v_asyncMode_2704_ = lean_ctor_get(v_toEnvExtension_2703_, 2);
v___x_2705_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2706_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2705_, v___x_2701_, v_env_2700_, v_asyncMode_2704_);
v_categories_2707_ = lean_ctor_get(v___x_2706_, 2);
lean_inc_ref(v_categories_2707_);
lean_dec(v___x_2706_);
v___x_2708_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_2709_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_2707_, v___x_2708_);
lean_dec_ref(v_categories_2707_);
if (lean_obj_tag(v___x_2709_) == 1)
{
lean_object* v_val_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2743_; 
v_val_2710_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2712_ = v___x_2709_;
v_isShared_2713_ = v_isSharedCheck_2743_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_val_2710_);
lean_dec(v___x_2709_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2743_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___y_2715_; lean_object* v___x_2724_; lean_object* v_toEnvExtension_2725_; lean_object* v_exportEntriesFn_2726_; lean_object* v_asyncMode_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v_importedEntries_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v_exported_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; uint8_t v___x_2739_; 
v___x_2724_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_2725_ = lean_ctor_get(v___x_2724_, 0);
v_exportEntriesFn_2726_ = lean_ctor_get(v___x_2724_, 4);
v_asyncMode_2727_ = lean_ctor_get(v_toEnvExtension_2725_, 2);
v___x_2728_ = lean_box(1);
v___x_2729_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_2730_ = lean_box(0);
lean_inc_ref_n(v_env_2700_, 2);
v___x_2731_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2729_, v_toEnvExtension_2725_, v_env_2700_, v_asyncMode_2727_, v___x_2730_);
v_importedEntries_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc_ref(v_importedEntries_2732_);
lean_dec(v___x_2731_);
v___x_2733_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2728_, v___x_2724_, v_env_2700_, v_asyncMode_2727_, v___x_2730_);
lean_inc_ref(v_exportEntriesFn_2726_);
v___x_2734_ = lean_apply_2(v_exportEntriesFn_2726_, v_env_2700_, v___x_2733_);
v_exported_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_exported_2735_);
lean_dec_ref(v___x_2734_);
v___x_2736_ = lean_array_push(v_importedEntries_2732_, v_exported_2735_);
v___x_2737_ = lean_unsigned_to_nat(0u);
v___x_2738_ = lean_array_get_size(v___x_2736_);
v___x_2739_ = lean_nat_dec_lt(v___x_2737_, v___x_2738_);
if (v___x_2739_ == 0)
{
lean_dec_ref(v___x_2736_);
v___y_2715_ = v___x_2728_;
goto v___jp_2714_;
}
else
{
size_t v___x_2740_; size_t v___x_2741_; lean_object* v___x_2742_; 
v___x_2740_ = ((size_t)0ULL);
v___x_2741_ = lean_usize_of_nat(v___x_2738_);
v___x_2742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_2736_, v___x_2740_, v___x_2741_, v___x_2728_);
lean_dec_ref(v___x_2736_);
v___y_2715_ = v___x_2742_;
goto v___jp_2714_;
}
v___jp_2714_:
{
lean_object* v_tables_2716_; lean_object* v_leadingTable_2717_; lean_object* v_trailingTable_2718_; lean_object* v_firstTokens_2719_; lean_object* v_firstTokens_2720_; lean_object* v___x_2722_; 
v_tables_2716_ = lean_ctor_get(v_val_2710_, 2);
v_leadingTable_2717_ = lean_ctor_get(v_tables_2716_, 0);
v_trailingTable_2718_ = lean_ctor_get(v_tables_2716_, 2);
lean_inc(v_trailingTable_2718_);
lean_inc(v_leadingTable_2717_);
lean_inc(v_val_2710_);
v_firstTokens_2719_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2710_, v_leadingTable_2717_, v___y_2715_);
v_firstTokens_2720_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2710_, v_trailingTable_2718_, v_firstTokens_2719_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set_tag(v___x_2712_, 0);
lean_ctor_set(v___x_2712_, 0, v_firstTokens_2720_);
v___x_2722_ = v___x_2712_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_firstTokens_2720_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
else
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
lean_dec(v___x_2709_);
lean_dec_ref(v_env_2700_);
v___x_2744_ = lean_box(1);
v___x_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
return v___x_2745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_2746_);
lean_dec(v___y_2746_);
return v_res_2748_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0(void){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = lean_box(1);
v___x_2750_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2749_);
return v___x_2750_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2(void){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2752_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1));
v___x_2753_ = l_Lean_stringToMessageData(v___x_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object* v_a_2754_, lean_object* v_a_2755_){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v_env_2760_; lean_object* v_env_2761_; lean_object* v_env_2762_; lean_object* v___x_2763_; lean_object* v_toEnvExtension_2764_; lean_object* v_exportEntriesFn_2765_; lean_object* v_asyncMode_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v_importedEntries_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2823_; 
v___x_2757_ = lean_st_ref_get(v_a_2755_);
v___x_2758_ = lean_st_ref_get(v_a_2755_);
v___x_2759_ = lean_st_ref_get(v_a_2755_);
v_env_2760_ = lean_ctor_get(v___x_2757_, 0);
lean_inc_ref(v_env_2760_);
lean_dec(v___x_2757_);
v_env_2761_ = lean_ctor_get(v___x_2758_, 0);
lean_inc_ref(v_env_2761_);
lean_dec(v___x_2758_);
v_env_2762_ = lean_ctor_get(v___x_2759_, 0);
lean_inc_ref(v_env_2762_);
lean_dec(v___x_2759_);
v___x_2763_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_2764_ = lean_ctor_get(v___x_2763_, 0);
v_exportEntriesFn_2765_ = lean_ctor_get(v___x_2763_, 4);
v_asyncMode_2766_ = lean_ctor_get(v_toEnvExtension_2764_, 2);
v___x_2767_ = lean_box(1);
v___x_2768_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_2769_ = lean_box(0);
v___x_2770_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2768_, v_toEnvExtension_2764_, v_env_2760_, v_asyncMode_2766_, v___x_2769_);
v_importedEntries_2771_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2823_ == 0)
{
lean_object* v_unused_2824_; 
v_unused_2824_ = lean_ctor_get(v___x_2770_, 1);
lean_dec(v_unused_2824_);
v___x_2773_ = v___x_2770_;
v_isShared_2774_ = v_isSharedCheck_2823_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_importedEntries_2771_);
lean_dec(v___x_2770_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2823_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v_exported_2777_; lean_object* v___x_2778_; size_t v_sz_2779_; size_t v___x_2780_; lean_object* v___x_2781_; 
v___x_2775_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2767_, v___x_2763_, v_env_2762_, v_asyncMode_2766_, v___x_2769_);
lean_inc_ref(v_exportEntriesFn_2765_);
v___x_2776_ = lean_apply_2(v_exportEntriesFn_2765_, v_env_2761_, v___x_2775_);
v_exported_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_exported_2777_);
lean_dec_ref(v___x_2776_);
v___x_2778_ = lean_array_push(v_importedEntries_2771_, v_exported_2777_);
v_sz_2779_ = lean_array_size(v___x_2778_);
v___x_2780_ = ((size_t)0ULL);
v___x_2781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v___x_2778_, v_sz_2779_, v___x_2780_, v___x_2767_, v_a_2754_, v_a_2755_);
lean_dec_ref(v___x_2778_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2783_; lean_object* v_a_2784_; lean_object* v___x_2785_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_a_2782_);
lean_dec_ref_known(v___x_2781_, 1);
v___x_2783_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v_a_2755_);
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_a_2784_);
lean_dec_ref(v___x_2783_);
v___x_2785_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v_a_2754_, v_a_2755_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_a_2786_);
lean_dec_ref_known(v___x_2785_, 1);
v___x_2787_ = lean_box(0);
v___x_2788_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_2784_, v_a_2782_, v_a_2786_, v___x_2787_, v_a_2754_, v_a_2755_);
lean_dec(v_a_2782_);
lean_dec(v_a_2784_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2794_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2788_, 1);
v___x_2790_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2);
v___x_2791_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2792_ = l_Lean_MessageData_joinSep(v_a_2789_, v___x_2791_);
if (v_isShared_2774_ == 0)
{
lean_ctor_set_tag(v___x_2773_, 7);
lean_ctor_set(v___x_2773_, 1, v___x_2792_);
lean_ctor_set(v___x_2773_, 0, v___x_2791_);
v___x_2794_ = v___x_2773_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2791_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v___x_2792_);
v___x_2794_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2795_ = l_Lean_MessageData_nestD(v___x_2794_);
v___x_2796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2790_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
v___x_2797_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v___x_2796_, v_a_2754_, v_a_2755_);
return v___x_2797_;
}
}
else
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
lean_del_object(v___x_2773_);
v_a_2799_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2788_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2788_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
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
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
lean_dec(v_a_2784_);
lean_dec(v_a_2782_);
lean_del_object(v___x_2773_);
v_a_2807_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2785_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2785_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_del_object(v___x_2773_);
v_a_2815_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2781_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2781_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_2825_, v_a_2826_);
lean_dec(v_a_2826_);
lean_dec_ref(v_a_2825_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object* v___stx_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_2830_, v_a_2831_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object* v___stx_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags(v___stx_2834_, v_a_2835_, v_a_2836_);
lean_dec(v_a_2836_);
lean_dec_ref(v_a_2835_);
lean_dec(v___stx_2834_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object* v_00_u03b4_2839_, lean_object* v_t_2840_, lean_object* v_k_2841_, lean_object* v_fallback_2842_){
_start:
{
lean_object* v___x_2843_; 
v___x_2843_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_2840_, v_k_2841_, v_fallback_2842_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object* v_00_u03b4_2844_, lean_object* v_t_2845_, lean_object* v_k_2846_, lean_object* v_fallback_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(v_00_u03b4_2844_, v_t_2845_, v_k_2846_, v_fallback_2847_);
lean_dec(v_fallback_2847_);
lean_dec(v_k_2846_);
lean_dec(v_t_2845_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object* v_as_2849_, size_t v_sz_2850_, size_t v_i_2851_, lean_object* v_b_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_2849_, v_sz_2850_, v_i_2851_, v_b_2852_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object* v_as_2857_, lean_object* v_sz_2858_, lean_object* v_i_2859_, lean_object* v_b_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
size_t v_sz_boxed_2864_; size_t v_i_boxed_2865_; lean_object* v_res_2866_; 
v_sz_boxed_2864_ = lean_unbox_usize(v_sz_2858_);
lean_dec(v_sz_2858_);
v_i_boxed_2865_ = lean_unbox_usize(v_i_2859_);
lean_dec(v_i_2859_);
v_res_2866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(v_as_2857_, v_sz_boxed_2864_, v_i_boxed_2865_, v_b_2860_, v___y_2861_, v___y_2862_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec_ref(v_as_2857_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_2868_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(v___y_2871_, v___y_2872_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object* v_val_2875_, lean_object* v___x_2876_, lean_object* v___x_2877_, lean_object* v_inst_2878_, lean_object* v_R_2879_, lean_object* v_a_2880_, lean_object* v_b_2881_){
_start:
{
lean_object* v___x_2882_; 
v___x_2882_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2875_, v___x_2876_, v___x_2877_, v_a_2880_, v_b_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object* v_val_2883_, lean_object* v___x_2884_, lean_object* v___x_2885_, lean_object* v_inst_2886_, lean_object* v_R_2887_, lean_object* v_a_2888_, lean_object* v_b_2889_){
_start:
{
lean_object* v_res_2890_; 
v_res_2890_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(v_val_2883_, v___x_2884_, v___x_2885_, v_inst_2886_, v_R_2887_, v_a_2888_, v_b_2889_);
lean_dec_ref(v___x_2884_);
lean_dec_ref(v_val_2883_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object* v_init_2891_, lean_object* v_t_2892_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_2891_, v_t_2892_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object* v_n_2894_, lean_object* v_as_2895_, lean_object* v_lo_2896_, lean_object* v_hi_2897_, lean_object* v_w_2898_, lean_object* v_hlo_2899_, lean_object* v_hhi_2900_){
_start:
{
lean_object* v___x_2901_; 
v___x_2901_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_2894_, v_as_2895_, v_lo_2896_, v_hi_2897_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object* v_n_2902_, lean_object* v_as_2903_, lean_object* v_lo_2904_, lean_object* v_hi_2905_, lean_object* v_w_2906_, lean_object* v_hlo_2907_, lean_object* v_hhi_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(v_n_2902_, v_as_2903_, v_lo_2904_, v_hi_2905_, v_w_2906_, v_hlo_2907_, v_hhi_2908_);
lean_dec(v_hi_2905_);
lean_dec(v_n_2902_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object* v_00_u03b2_2910_, lean_object* v_x_2911_, lean_object* v_x_2912_){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_2911_, v_x_2912_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2914_, lean_object* v_x_2915_, lean_object* v_x_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(v_00_u03b2_2914_, v_x_2915_, v_x_2916_);
lean_dec(v_x_2916_);
lean_dec_ref(v_x_2915_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object* v_tac_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_2918_, v___y_2920_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object* v_tac_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(v_tac_2923_, v___y_2924_, v___y_2925_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object* v_00_u03b4_2928_, lean_object* v_t_2929_, lean_object* v_k_2930_){
_start:
{
lean_object* v___x_2931_; 
v___x_2931_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_2929_, v_k_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___boxed(lean_object* v_00_u03b4_2932_, lean_object* v_t_2933_, lean_object* v_k_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(v_00_u03b4_2932_, v_t_2933_, v_k_2934_);
lean_dec(v_k_2934_);
lean_dec(v_t_2933_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object* v_00_u03b2_2936_, lean_object* v_x_2937_, lean_object* v_x_2938_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_2937_, v_x_2938_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object* v_00_u03b2_2940_, lean_object* v_x_2941_, lean_object* v_x_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(v_00_u03b2_2940_, v_x_2941_, v_x_2942_);
lean_dec(v_x_2942_);
lean_dec_ref(v_x_2941_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(lean_object* v_n_2944_, lean_object* v_lo_2945_, lean_object* v_hi_2946_, lean_object* v_hhi_2947_, lean_object* v_pivot_2948_, lean_object* v_as_2949_, lean_object* v_i_2950_, lean_object* v_k_2951_, lean_object* v_ilo_2952_, lean_object* v_ik_2953_, lean_object* v_w_2954_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_2946_, v_pivot_2948_, v_as_2949_, v_i_2950_, v_k_2951_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___boxed(lean_object* v_n_2956_, lean_object* v_lo_2957_, lean_object* v_hi_2958_, lean_object* v_hhi_2959_, lean_object* v_pivot_2960_, lean_object* v_as_2961_, lean_object* v_i_2962_, lean_object* v_k_2963_, lean_object* v_ilo_2964_, lean_object* v_ik_2965_, lean_object* v_w_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(v_n_2956_, v_lo_2957_, v_hi_2958_, v_hhi_2959_, v_pivot_2960_, v_as_2961_, v_i_2962_, v_k_2963_, v_ilo_2964_, v_ik_2965_, v_w_2966_);
lean_dec(v_hi_2958_);
lean_dec(v_lo_2957_);
lean_dec(v_n_2956_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(lean_object* v_as_2968_, size_t v_sz_2969_, size_t v_i_2970_, lean_object* v_b_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_2968_, v_sz_2969_, v_i_2970_, v_b_2971_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___boxed(lean_object* v_as_2976_, lean_object* v_sz_2977_, lean_object* v_i_2978_, lean_object* v_b_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
size_t v_sz_boxed_2983_; size_t v_i_boxed_2984_; lean_object* v_res_2985_; 
v_sz_boxed_2983_ = lean_unbox_usize(v_sz_2977_);
lean_dec(v_sz_2977_);
v_i_boxed_2984_ = lean_unbox_usize(v_i_2978_);
lean_dec(v_i_2978_);
v_res_2985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(v_as_2976_, v_sz_boxed_2983_, v_i_boxed_2984_, v_b_2979_, v___y_2980_, v___y_2981_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec_ref(v_as_2976_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object* v_init_2986_, lean_object* v_t_2987_){
_start:
{
lean_object* v___x_2988_; 
v___x_2988_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_2986_, v_t_2987_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object* v_init_2989_, lean_object* v_t_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(v_init_2989_, v_t_2990_);
lean_dec(v_t_2990_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object* v_n_2992_, lean_object* v_as_2993_, lean_object* v_lo_2994_, lean_object* v_hi_2995_, lean_object* v_w_2996_, lean_object* v_hlo_2997_, lean_object* v_hhi_2998_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_2992_, v_as_2993_, v_lo_2994_, v_hi_2995_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object* v_n_3000_, lean_object* v_as_3001_, lean_object* v_lo_3002_, lean_object* v_hi_3003_, lean_object* v_w_3004_, lean_object* v_hlo_3005_, lean_object* v_hhi_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(v_n_3000_, v_as_3001_, v_lo_3002_, v_hi_3003_, v_w_3004_, v_hlo_3005_, v_hhi_3006_);
lean_dec(v_hi_3003_);
lean_dec(v_n_3000_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object* v_init_3008_, lean_object* v_x_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_3008_, v_x_3009_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object* v_init_3014_, lean_object* v_x_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(v_init_3014_, v_x_3015_, v___y_3016_, v___y_3017_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_3020_, lean_object* v_x_3021_, size_t v_x_3022_, lean_object* v_x_3023_){
_start:
{
lean_object* v___x_3024_; 
v___x_3024_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3021_, v_x_3022_, v_x_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3025_, lean_object* v_x_3026_, lean_object* v_x_3027_, lean_object* v_x_3028_){
_start:
{
size_t v_x_18928__boxed_3029_; lean_object* v_res_3030_; 
v_x_18928__boxed_3029_ = lean_unbox_usize(v_x_3027_);
lean_dec(v_x_3027_);
v_res_3030_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(v_00_u03b2_3025_, v_x_3026_, v_x_18928__boxed_3029_, v_x_3028_);
lean_dec(v_x_3028_);
lean_dec_ref(v_x_3026_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object* v_as_3031_, lean_object* v_k_3032_, lean_object* v_x_3033_, lean_object* v_x_3034_, lean_object* v_x_3035_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_3031_, v_k_3032_, v_x_3033_, v_x_3034_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object* v_as_3037_, lean_object* v_k_3038_, lean_object* v_x_3039_, lean_object* v_x_3040_, lean_object* v_x_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(v_as_3037_, v_k_3038_, v_x_3039_, v_x_3040_, v_x_3041_);
lean_dec_ref(v_k_3038_);
lean_dec_ref(v_as_3037_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(lean_object* v_00_u03b2_3043_, lean_object* v_m_3044_, lean_object* v_a_3045_){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_3044_, v_a_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___boxed(lean_object* v_00_u03b2_3047_, lean_object* v_m_3048_, lean_object* v_a_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(v_00_u03b2_3047_, v_m_3048_, v_a_3049_);
lean_dec(v_a_3049_);
lean_dec_ref(v_m_3048_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(lean_object* v_n_3051_, lean_object* v_lo_3052_, lean_object* v_hi_3053_, lean_object* v_hhi_3054_, lean_object* v_pivot_3055_, lean_object* v_as_3056_, lean_object* v_i_3057_, lean_object* v_k_3058_, lean_object* v_ilo_3059_, lean_object* v_ik_3060_, lean_object* v_w_3061_){
_start:
{
lean_object* v___x_3062_; 
v___x_3062_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_3053_, v_pivot_3055_, v_as_3056_, v_i_3057_, v_k_3058_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___boxed(lean_object* v_n_3063_, lean_object* v_lo_3064_, lean_object* v_hi_3065_, lean_object* v_hhi_3066_, lean_object* v_pivot_3067_, lean_object* v_as_3068_, lean_object* v_i_3069_, lean_object* v_k_3070_, lean_object* v_ilo_3071_, lean_object* v_ik_3072_, lean_object* v_w_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(v_n_3063_, v_lo_3064_, v_hi_3065_, v_hhi_3066_, v_pivot_3067_, v_as_3068_, v_i_3069_, v_k_3070_, v_ilo_3071_, v_ik_3072_, v_w_3073_);
lean_dec(v_hi_3065_);
lean_dec(v_lo_3064_);
lean_dec(v_n_3063_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_3075_, lean_object* v_keys_3076_, lean_object* v_vals_3077_, lean_object* v_heq_3078_, lean_object* v_i_3079_, lean_object* v_k_3080_){
_start:
{
lean_object* v___x_3081_; 
v___x_3081_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_3076_, v_vals_3077_, v_i_3079_, v_k_3080_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object* v_00_u03b2_3082_, lean_object* v_keys_3083_, lean_object* v_vals_3084_, lean_object* v_heq_3085_, lean_object* v_i_3086_, lean_object* v_k_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(v_00_u03b2_3082_, v_keys_3083_, v_vals_3084_, v_heq_3085_, v_i_3086_, v_k_3087_);
lean_dec(v_k_3087_);
lean_dec_ref(v_vals_3084_);
lean_dec_ref(v_keys_3083_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(lean_object* v_00_u03b2_3089_, lean_object* v_a_3090_, lean_object* v_x_3091_){
_start:
{
lean_object* v___x_3092_; 
v___x_3092_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_3090_, v_x_3091_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___boxed(lean_object* v_00_u03b2_3093_, lean_object* v_a_3094_, lean_object* v_x_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(v_00_u03b2_3093_, v_a_3094_, v_x_3095_);
lean_dec(v_x_3095_);
lean_dec(v_a_3094_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1(){
_start:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3111_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3112_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1));
v___x_3113_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3114_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed), 4, 0);
v___x_3115_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3111_, v___x_3112_, v___x_3113_, v___x_3114_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object* v_a_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3(){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3120_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3121_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0));
v___x_3122_ = l_Lean_addBuiltinDocString(v___x_3120_, v___x_3121_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object* v_a_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5(){
_start:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3151_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3152_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6));
v___x_3153_ = l_Lean_addBuiltinDeclarationRanges(v___x_3151_, v___x_3152_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object* v_a_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object* v_env_3156_, lean_object* v___x_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, uint8_t v_includeUnnamed_3160_, lean_object* v_x_3161_, lean_object* v_____s_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
lean_object* v_fst_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3223_; 
v_fst_3168_ = lean_ctor_get(v_x_3161_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v_x_3161_);
if (v_isSharedCheck_3223_ == 0)
{
lean_object* v_unused_3224_; 
v_unused_3224_ = lean_ctor_get(v_x_3161_, 1);
lean_dec(v_unused_3224_);
v___x_3170_ = v_x_3161_;
v_isShared_3171_ = v_isSharedCheck_3223_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_fst_3168_);
lean_dec(v_x_3161_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3223_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v_userName_3173_; lean_object* v___y_3174_; lean_object* v___x_3208_; 
lean_inc(v_fst_3168_);
lean_inc_ref(v_env_3156_);
v___x_3208_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_3156_, v_fst_3168_);
if (lean_obj_tag(v___x_3208_) == 1)
{
lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3216_; 
lean_del_object(v___x_3170_);
lean_dec(v_fst_3168_);
lean_dec(v___x_3157_);
lean_dec_ref(v_env_3156_);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3216_ == 0)
{
lean_object* v_unused_3217_; 
v_unused_3217_ = lean_ctor_get(v___x_3208_, 0);
lean_dec(v_unused_3217_);
v___x_3210_ = v___x_3208_;
v_isShared_3211_ = v_isSharedCheck_3216_;
goto v_resetjp_3209_;
}
else
{
lean_dec(v___x_3208_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3216_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 0, v_____s_3162_);
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_____s_3162_);
v___x_3213_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
lean_object* v___x_3214_; 
v___x_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
return v___x_3214_;
}
}
}
else
{
lean_object* v___x_3218_; 
lean_dec(v___x_3208_);
v___x_3218_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_a_3159_, v_fst_3168_);
if (lean_obj_tag(v___x_3218_) == 1)
{
lean_object* v_val_3219_; 
v_val_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_val_3219_);
lean_dec_ref_known(v___x_3218_, 1);
v_userName_3173_ = v_val_3219_;
v___y_3174_ = v___y_3165_;
goto v___jp_3172_;
}
else
{
lean_dec(v___x_3218_);
if (v_includeUnnamed_3160_ == 0)
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
lean_del_object(v___x_3170_);
lean_dec(v_fst_3168_);
lean_dec(v___x_3157_);
lean_dec_ref(v_env_3156_);
v___x_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3220_, 0, v_____s_3162_);
v___x_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
return v___x_3221_;
}
else
{
lean_object* v___x_3222_; 
lean_inc(v_fst_3168_);
v___x_3222_ = l_Lean_Name_toString(v_fst_3168_, v_includeUnnamed_3160_);
v_userName_3173_ = v___x_3222_;
v___y_3174_ = v___y_3165_;
goto v___jp_3172_;
}
}
}
v___jp_3172_:
{
uint8_t v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3175_ = 1;
v___x_3176_ = l_Lean_Options_empty;
v___x_3177_ = lean_box(0);
lean_inc(v_fst_3168_);
lean_inc_ref(v_env_3156_);
v___x_3178_ = l_Lean_findDocString_x3f(v_env_3156_, v_fst_3168_, v___x_3175_, v___x_3176_, v___x_3157_, v___x_3177_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3192_; 
lean_del_object(v___x_3170_);
v_a_3179_ = lean_ctor_get(v___x_3178_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3181_ = v___x_3178_;
v_isShared_3182_ = v_isSharedCheck_3192_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3178_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3192_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3190_; 
v___x_3183_ = l_Lean_NameSet_empty;
v___x_3184_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_a_3158_, v_fst_3168_, v___x_3183_);
lean_inc(v_fst_3168_);
v___x_3185_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_3156_, v_fst_3168_);
v___x_3186_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3186_, 0, v_fst_3168_);
lean_ctor_set(v___x_3186_, 1, v_userName_3173_);
lean_ctor_set(v___x_3186_, 2, v___x_3184_);
lean_ctor_set(v___x_3186_, 3, v_a_3179_);
lean_ctor_set(v___x_3186_, 4, v___x_3185_);
v___x_3187_ = lean_array_push(v_____s_3162_, v___x_3186_);
v___x_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3187_);
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 0, v___x_3188_);
v___x_3190_ = v___x_3181_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3188_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3207_; 
lean_dec_ref(v_userName_3173_);
lean_dec(v_fst_3168_);
lean_dec_ref(v_____s_3162_);
lean_dec_ref(v_env_3156_);
v_a_3193_ = lean_ctor_get(v___x_3178_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3195_ = v___x_3178_;
v_isShared_3196_ = v_isSharedCheck_3207_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3178_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3207_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v_ref_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3202_; 
v_ref_3197_ = lean_ctor_get(v___y_3174_, 5);
v___x_3198_ = lean_io_error_to_string(v_a_3193_);
v___x_3199_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3198_);
v___x_3200_ = l_Lean_MessageData_ofFormat(v___x_3199_);
lean_inc(v_ref_3197_);
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 1, v___x_3200_);
lean_ctor_set(v___x_3170_, 0, v_ref_3197_);
v___x_3202_ = v___x_3170_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_ref_3197_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v___x_3200_);
v___x_3202_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
lean_object* v___x_3204_; 
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 0, v___x_3202_);
v___x_3204_ = v___x_3195_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3202_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object* v_env_3225_, lean_object* v___x_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_includeUnnamed_3229_, lean_object* v_x_3230_, lean_object* v_____s_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
uint8_t v_includeUnnamed_boxed_3237_; lean_object* v_res_3238_; 
v_includeUnnamed_boxed_3237_ = lean_unbox(v_includeUnnamed_3229_);
v_res_3238_ = l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(v_env_3225_, v___x_3226_, v_a_3227_, v_a_3228_, v_includeUnnamed_boxed_3237_, v_x_3230_, v_____s_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec(v_a_3228_);
lean_dec(v_a_3227_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object* v_as_3239_, size_t v_sz_3240_, size_t v_i_3241_, lean_object* v_b_3242_){
_start:
{
uint8_t v___x_3244_; 
v___x_3244_ = lean_usize_dec_lt(v_i_3241_, v_sz_3240_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; 
v___x_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3245_, 0, v_b_3242_);
return v___x_3245_;
}
else
{
lean_object* v_a_3246_; lean_object* v_fst_3247_; lean_object* v_snd_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; size_t v___x_3253_; size_t v___x_3254_; 
v_a_3246_ = lean_array_uget_borrowed(v_as_3239_, v_i_3241_);
v_fst_3247_ = lean_ctor_get(v_a_3246_, 0);
v_snd_3248_ = lean_ctor_get(v_a_3246_, 1);
v___x_3249_ = l_Lean_NameSet_empty;
v___x_3250_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_3242_, v_fst_3247_, v___x_3249_);
lean_inc(v_snd_3248_);
v___x_3251_ = l_Lean_NameSet_insert(v___x_3250_, v_snd_3248_);
lean_inc(v_fst_3247_);
v___x_3252_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3247_, v___x_3251_, v_b_3242_);
v___x_3253_ = ((size_t)1ULL);
v___x_3254_ = lean_usize_add(v_i_3241_, v___x_3253_);
v_i_3241_ = v___x_3254_;
v_b_3242_ = v___x_3252_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object* v_as_3256_, lean_object* v_sz_3257_, lean_object* v_i_3258_, lean_object* v_b_3259_, lean_object* v___y_3260_){
_start:
{
size_t v_sz_boxed_3261_; size_t v_i_boxed_3262_; lean_object* v_res_3263_; 
v_sz_boxed_3261_ = lean_unbox_usize(v_sz_3257_);
lean_dec(v_sz_3257_);
v_i_boxed_3262_ = lean_unbox_usize(v_i_3258_);
lean_dec(v_i_3258_);
v_res_3263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_3256_, v_sz_boxed_3261_, v_i_boxed_3262_, v_b_3259_);
lean_dec_ref(v_as_3256_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object* v_as_3264_, size_t v_sz_3265_, size_t v_i_3266_, lean_object* v_b_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
uint8_t v___x_3273_; 
v___x_3273_ = lean_usize_dec_lt(v_i_3266_, v_sz_3265_);
if (v___x_3273_ == 0)
{
lean_object* v___x_3274_; 
v___x_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3274_, 0, v_b_3267_);
return v___x_3274_;
}
else
{
lean_object* v_a_3275_; size_t v_sz_3276_; size_t v___x_3277_; lean_object* v___x_3278_; 
v_a_3275_ = lean_array_uget_borrowed(v_as_3264_, v_i_3266_);
v_sz_3276_ = lean_array_size(v_a_3275_);
v___x_3277_ = ((size_t)0ULL);
v___x_3278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_a_3275_, v_sz_3276_, v___x_3277_, v_b_3267_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_a_3279_; size_t v___x_3280_; size_t v___x_3281_; 
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_a_3279_);
lean_dec_ref_known(v___x_3278_, 1);
v___x_3280_ = ((size_t)1ULL);
v___x_3281_ = lean_usize_add(v_i_3266_, v___x_3280_);
v_i_3266_ = v___x_3281_;
v_b_3267_ = v_a_3279_;
goto _start;
}
else
{
return v___x_3278_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object* v_as_3283_, lean_object* v_sz_3284_, lean_object* v_i_3285_, lean_object* v_b_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
size_t v_sz_boxed_3292_; size_t v_i_boxed_3293_; lean_object* v_res_3294_; 
v_sz_boxed_3292_ = lean_unbox_usize(v_sz_3284_);
lean_dec(v_sz_3284_);
v_i_boxed_3293_ = lean_unbox_usize(v_i_3285_);
lean_dec(v_i_3285_);
v_res_3294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v_as_3283_, v_sz_boxed_3292_, v_i_boxed_3293_, v_b_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_);
lean_dec(v___y_3290_);
lean_dec_ref(v___y_3289_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec_ref(v_as_3283_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object* v_f_3295_, lean_object* v_keys_3296_, lean_object* v_vals_3297_, lean_object* v_i_3298_, lean_object* v_acc_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v___x_3305_; uint8_t v___x_3306_; 
v___x_3305_ = lean_array_get_size(v_keys_3296_);
v___x_3306_ = lean_nat_dec_lt(v_i_3298_, v___x_3305_);
if (v___x_3306_ == 0)
{
lean_object* v___x_3307_; lean_object* v___x_3308_; 
lean_dec(v_i_3298_);
lean_dec_ref(v_f_3295_);
v___x_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3307_, 0, v_acc_3299_);
v___x_3308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3307_);
return v___x_3308_;
}
else
{
lean_object* v_k_3309_; lean_object* v_v_3310_; lean_object* v___x_3311_; 
v_k_3309_ = lean_array_fget_borrowed(v_keys_3296_, v_i_3298_);
v_v_3310_ = lean_array_fget_borrowed(v_vals_3297_, v_i_3298_);
lean_inc_ref(v_f_3295_);
lean_inc(v___y_3303_);
lean_inc_ref(v___y_3302_);
lean_inc(v___y_3301_);
lean_inc_ref(v___y_3300_);
lean_inc(v_v_3310_);
lean_inc(v_k_3309_);
v___x_3311_ = lean_apply_8(v_f_3295_, v_acc_3299_, v_k_3309_, v_v_3310_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, lean_box(0));
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_a_3312_);
if (lean_obj_tag(v_a_3312_) == 0)
{
lean_dec_ref_known(v_a_3312_, 1);
lean_dec(v_i_3298_);
lean_dec_ref(v_f_3295_);
return v___x_3311_;
}
else
{
lean_object* v_a_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
lean_dec_ref_known(v___x_3311_, 1);
v_a_3313_ = lean_ctor_get(v_a_3312_, 0);
lean_inc(v_a_3313_);
lean_dec_ref_known(v_a_3312_, 1);
v___x_3314_ = lean_unsigned_to_nat(1u);
v___x_3315_ = lean_nat_add(v_i_3298_, v___x_3314_);
lean_dec(v_i_3298_);
v_i_3298_ = v___x_3315_;
v_acc_3299_ = v_a_3313_;
goto _start;
}
}
else
{
lean_dec(v_i_3298_);
lean_dec_ref(v_f_3295_);
return v___x_3311_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_f_3317_, lean_object* v_keys_3318_, lean_object* v_vals_3319_, lean_object* v_i_3320_, lean_object* v_acc_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3317_, v_keys_3318_, v_vals_3319_, v_i_3320_, v_acc_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec_ref(v_vals_3319_);
lean_dec_ref(v_keys_3318_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_f_3328_, lean_object* v_as_3329_, size_t v_i_3330_, size_t v_stop_3331_, lean_object* v_b_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_){
_start:
{
lean_object* v_a_3339_; lean_object* v___y_3344_; uint8_t v___x_3347_; 
v___x_3347_ = lean_usize_dec_eq(v_i_3330_, v_stop_3331_);
if (v___x_3347_ == 0)
{
lean_object* v___x_3348_; 
v___x_3348_ = lean_array_uget_borrowed(v_as_3329_, v_i_3330_);
switch(lean_obj_tag(v___x_3348_))
{
case 0:
{
lean_object* v_key_3349_; lean_object* v_val_3350_; lean_object* v___x_3351_; 
v_key_3349_ = lean_ctor_get(v___x_3348_, 0);
v_val_3350_ = lean_ctor_get(v___x_3348_, 1);
lean_inc_ref(v_f_3328_);
lean_inc(v___y_3336_);
lean_inc_ref(v___y_3335_);
lean_inc(v___y_3334_);
lean_inc_ref(v___y_3333_);
lean_inc(v_val_3350_);
lean_inc(v_key_3349_);
v___x_3351_ = lean_apply_8(v_f_3328_, v_b_3332_, v_key_3349_, v_val_3350_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, lean_box(0));
v___y_3344_ = v___x_3351_;
goto v___jp_3343_;
}
case 1:
{
lean_object* v_node_3352_; lean_object* v___x_3353_; 
v_node_3352_ = lean_ctor_get(v___x_3348_, 0);
lean_inc(v_node_3352_);
lean_inc_ref(v_f_3328_);
v___x_3353_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3328_, v_node_3352_, v_b_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
v___y_3344_ = v___x_3353_;
goto v___jp_3343_;
}
default: 
{
v_a_3339_ = v_b_3332_;
goto v___jp_3338_;
}
}
}
else
{
lean_object* v___x_3354_; lean_object* v___x_3355_; 
lean_dec_ref(v_f_3328_);
v___x_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3354_, 0, v_b_3332_);
v___x_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3354_);
return v___x_3355_;
}
v___jp_3338_:
{
size_t v___x_3340_; size_t v___x_3341_; 
v___x_3340_ = ((size_t)1ULL);
v___x_3341_ = lean_usize_add(v_i_3330_, v___x_3340_);
v_i_3330_ = v___x_3341_;
v_b_3332_ = v_a_3339_;
goto _start;
}
v___jp_3343_:
{
if (lean_obj_tag(v___y_3344_) == 0)
{
lean_object* v_a_3345_; 
v_a_3345_ = lean_ctor_get(v___y_3344_, 0);
if (lean_obj_tag(v_a_3345_) == 0)
{
lean_dec_ref(v_f_3328_);
return v___y_3344_;
}
else
{
lean_object* v_a_3346_; 
lean_inc_ref(v_a_3345_);
lean_dec_ref_known(v___y_3344_, 1);
v_a_3346_ = lean_ctor_get(v_a_3345_, 0);
lean_inc(v_a_3346_);
lean_dec_ref_known(v_a_3345_, 1);
v_a_3339_ = v_a_3346_;
goto v___jp_3338_;
}
}
else
{
lean_dec_ref(v_f_3328_);
return v___y_3344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object* v_f_3356_, lean_object* v_x_3357_, lean_object* v_x_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_){
_start:
{
if (lean_obj_tag(v_x_3357_) == 0)
{
lean_object* v_es_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3378_; 
v_es_3364_ = lean_ctor_get(v_x_3357_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v_x_3357_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3366_ = v_x_3357_;
v_isShared_3367_ = v_isSharedCheck_3378_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_es_3364_);
lean_dec(v_x_3357_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3378_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3368_; lean_object* v___x_3369_; uint8_t v___x_3370_; 
v___x_3368_ = lean_unsigned_to_nat(0u);
v___x_3369_ = lean_array_get_size(v_es_3364_);
v___x_3370_ = lean_nat_dec_lt(v___x_3368_, v___x_3369_);
if (v___x_3370_ == 0)
{
lean_object* v___x_3372_; 
lean_dec_ref(v_es_3364_);
lean_dec_ref(v_f_3356_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set_tag(v___x_3366_, 1);
lean_ctor_set(v___x_3366_, 0, v_x_3358_);
v___x_3372_ = v___x_3366_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_x_3358_);
v___x_3372_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
lean_object* v___x_3373_; 
v___x_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3372_);
return v___x_3373_;
}
}
else
{
size_t v___x_3375_; size_t v___x_3376_; lean_object* v___x_3377_; 
lean_del_object(v___x_3366_);
v___x_3375_ = ((size_t)0ULL);
v___x_3376_ = lean_usize_of_nat(v___x_3369_);
v___x_3377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3356_, v_es_3364_, v___x_3375_, v___x_3376_, v_x_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
lean_dec_ref(v_es_3364_);
return v___x_3377_;
}
}
}
else
{
lean_object* v_ks_3379_; lean_object* v_vs_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v_ks_3379_ = lean_ctor_get(v_x_3357_, 0);
lean_inc_ref(v_ks_3379_);
v_vs_3380_ = lean_ctor_get(v_x_3357_, 1);
lean_inc_ref(v_vs_3380_);
lean_dec_ref_known(v_x_3357_, 2);
v___x_3381_ = lean_unsigned_to_nat(0u);
v___x_3382_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3356_, v_ks_3379_, v_vs_3380_, v___x_3381_, v_x_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
lean_dec_ref(v_vs_3380_);
lean_dec_ref(v_ks_3379_);
return v___x_3382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_f_3383_, lean_object* v_x_3384_, lean_object* v_x_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3383_, v_x_3384_, v_x_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_3392_, lean_object* v_as_3393_, lean_object* v_i_3394_, lean_object* v_stop_3395_, lean_object* v_b_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
size_t v_i_boxed_3402_; size_t v_stop_boxed_3403_; lean_object* v_res_3404_; 
v_i_boxed_3402_ = lean_unbox_usize(v_i_3394_);
lean_dec(v_i_3394_);
v_stop_boxed_3403_ = lean_unbox_usize(v_stop_3395_);
lean_dec(v_stop_3395_);
v_res_3404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3392_, v_as_3393_, v_i_boxed_3402_, v_stop_boxed_3403_, v_b_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec_ref(v_as_3393_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object* v_f_3405_, lean_object* v_s_3406_, lean_object* v_a_3407_, lean_object* v_b_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3414_, 0, v_a_3407_);
lean_ctor_set(v___x_3414_, 1, v_b_3408_);
lean_inc(v___y_3412_);
lean_inc_ref(v___y_3411_);
lean_inc(v___y_3410_);
lean_inc_ref(v___y_3409_);
v___x_3415_ = lean_apply_7(v_f_3405_, v___x_3414_, v_s_3406_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, lean_box(0));
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3442_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3418_ = v___x_3415_;
v_isShared_3419_ = v_isSharedCheck_3442_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3415_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3442_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
if (lean_obj_tag(v_a_3416_) == 0)
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3430_; 
v_a_3420_ = lean_ctor_get(v_a_3416_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v_a_3416_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3422_ = v_a_3416_;
v_isShared_3423_ = v_isSharedCheck_3430_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v_a_3416_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3430_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3423_ == 0)
{
v___x_3425_ = v___x_3422_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3420_);
v___x_3425_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
lean_object* v___x_3427_; 
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_3425_);
v___x_3427_ = v___x_3418_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3425_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
}
else
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3441_; 
v_a_3431_ = lean_ctor_get(v_a_3416_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v_a_3416_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3433_ = v_a_3416_;
v_isShared_3434_ = v_isSharedCheck_3441_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v_a_3416_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3441_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
if (v_isShared_3434_ == 0)
{
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3431_);
v___x_3436_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
lean_object* v___x_3438_; 
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_3436_);
v___x_3438_ = v___x_3418_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3436_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
}
}
}
else
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3450_; 
v_a_3443_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3445_ = v___x_3415_;
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3415_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3443_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object* v_f_3451_, lean_object* v_s_3452_, lean_object* v_a_3453_, lean_object* v_b_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(v_f_3451_, v_s_3452_, v_a_3453_, v_b_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object* v_map_3461_, lean_object* v_init_3462_, lean_object* v_f_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
lean_object* v___f_3469_; lean_object* v___x_3470_; 
v___f_3469_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3469_, 0, v_f_3463_);
lean_inc_ref(v_map_3461_);
v___x_3470_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v___f_3469_, v_map_3461_, v_init_3462_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_);
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3479_; 
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3473_ = v___x_3470_;
v_isShared_3474_ = v_isSharedCheck_3479_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3470_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3479_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v_a_3475_; lean_object* v___x_3477_; 
v_a_3475_ = lean_ctor_get(v_a_3471_, 0);
lean_inc(v_a_3475_);
lean_dec(v_a_3471_);
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 0, v_a_3475_);
v___x_3477_ = v___x_3473_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3475_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
else
{
lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3487_; 
v_a_3480_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3482_ = v___x_3470_;
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_3470_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3485_; 
if (v_isShared_3483_ == 0)
{
v___x_3485_ = v___x_3482_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_a_3480_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object* v_map_3488_, lean_object* v_init_3489_, lean_object* v_f_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
lean_object* v_res_3496_; 
v_res_3496_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_3488_, v_init_3489_, v_f_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec_ref(v_map_3488_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object* v___y_3497_){
_start:
{
lean_object* v___x_3499_; lean_object* v_env_3500_; lean_object* v___x_3501_; lean_object* v_ext_3502_; lean_object* v_toEnvExtension_3503_; lean_object* v_asyncMode_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v_categories_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3499_ = lean_st_ref_get(v___y_3497_);
v_env_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc_ref_n(v_env_3500_, 2);
lean_dec(v___x_3499_);
v___x_3501_ = l_Lean_Parser_parserExtension;
v_ext_3502_ = lean_ctor_get(v___x_3501_, 1);
v_toEnvExtension_3503_ = lean_ctor_get(v_ext_3502_, 0);
v_asyncMode_3504_ = lean_ctor_get(v_toEnvExtension_3503_, 2);
v___x_3505_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3506_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3505_, v___x_3501_, v_env_3500_, v_asyncMode_3504_);
v_categories_3507_ = lean_ctor_get(v___x_3506_, 2);
lean_inc_ref(v_categories_3507_);
lean_dec(v___x_3506_);
v___x_3508_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3509_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3507_, v___x_3508_);
lean_dec_ref(v_categories_3507_);
if (lean_obj_tag(v___x_3509_) == 1)
{
lean_object* v_val_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3543_; 
v_val_3510_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3512_ = v___x_3509_;
v_isShared_3513_ = v_isSharedCheck_3543_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_val_3510_);
lean_dec(v___x_3509_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3543_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___y_3515_; lean_object* v___x_3524_; lean_object* v_toEnvExtension_3525_; lean_object* v_exportEntriesFn_3526_; lean_object* v_asyncMode_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v_importedEntries_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v_exported_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; uint8_t v___x_3539_; 
v___x_3524_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3525_ = lean_ctor_get(v___x_3524_, 0);
v_exportEntriesFn_3526_ = lean_ctor_get(v___x_3524_, 4);
v_asyncMode_3527_ = lean_ctor_get(v_toEnvExtension_3525_, 2);
v___x_3528_ = lean_box(1);
v___x_3529_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3530_ = lean_box(0);
lean_inc_ref_n(v_env_3500_, 2);
v___x_3531_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3529_, v_toEnvExtension_3525_, v_env_3500_, v_asyncMode_3527_, v___x_3530_);
v_importedEntries_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc_ref(v_importedEntries_3532_);
lean_dec(v___x_3531_);
v___x_3533_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3528_, v___x_3524_, v_env_3500_, v_asyncMode_3527_, v___x_3530_);
lean_inc_ref(v_exportEntriesFn_3526_);
v___x_3534_ = lean_apply_2(v_exportEntriesFn_3526_, v_env_3500_, v___x_3533_);
v_exported_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_exported_3535_);
lean_dec_ref(v___x_3534_);
v___x_3536_ = lean_array_push(v_importedEntries_3532_, v_exported_3535_);
v___x_3537_ = lean_unsigned_to_nat(0u);
v___x_3538_ = lean_array_get_size(v___x_3536_);
v___x_3539_ = lean_nat_dec_lt(v___x_3537_, v___x_3538_);
if (v___x_3539_ == 0)
{
lean_dec_ref(v___x_3536_);
v___y_3515_ = v___x_3528_;
goto v___jp_3514_;
}
else
{
size_t v___x_3540_; size_t v___x_3541_; lean_object* v___x_3542_; 
v___x_3540_ = ((size_t)0ULL);
v___x_3541_ = lean_usize_of_nat(v___x_3538_);
v___x_3542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3536_, v___x_3540_, v___x_3541_, v___x_3528_);
lean_dec_ref(v___x_3536_);
v___y_3515_ = v___x_3542_;
goto v___jp_3514_;
}
v___jp_3514_:
{
lean_object* v_tables_3516_; lean_object* v_leadingTable_3517_; lean_object* v_trailingTable_3518_; lean_object* v_firstTokens_3519_; lean_object* v_firstTokens_3520_; lean_object* v___x_3522_; 
v_tables_3516_ = lean_ctor_get(v_val_3510_, 2);
v_leadingTable_3517_ = lean_ctor_get(v_tables_3516_, 0);
v_trailingTable_3518_ = lean_ctor_get(v_tables_3516_, 2);
lean_inc(v_trailingTable_3518_);
lean_inc(v_leadingTable_3517_);
lean_inc(v_val_3510_);
v_firstTokens_3519_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3510_, v_leadingTable_3517_, v___y_3515_);
v_firstTokens_3520_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3510_, v_trailingTable_3518_, v_firstTokens_3519_);
if (v_isShared_3513_ == 0)
{
lean_ctor_set_tag(v___x_3512_, 0);
lean_ctor_set(v___x_3512_, 0, v_firstTokens_3520_);
v___x_3522_ = v___x_3512_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_firstTokens_3520_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
else
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
lean_dec(v___x_3509_);
lean_dec_ref(v_env_3500_);
v___x_3544_ = lean_box(1);
v___x_3545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3544_);
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
lean_object* v___x_3557_; lean_object* v_env_3558_; lean_object* v___x_3559_; lean_object* v_toEnvExtension_3560_; lean_object* v_exportEntriesFn_3561_; lean_object* v_asyncMode_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v_importedEntries_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v_exported_3570_; lean_object* v___x_3571_; size_t v_sz_3572_; size_t v___x_3573_; lean_object* v___x_3574_; 
v___x_3557_ = lean_st_ref_get(v_a_3555_);
v_env_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc_ref_n(v_env_3558_, 4);
lean_dec(v___x_3557_);
v___x_3559_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_3560_ = lean_ctor_get(v___x_3559_, 0);
v_exportEntriesFn_3561_ = lean_ctor_get(v___x_3559_, 4);
v_asyncMode_3562_ = lean_ctor_get(v_toEnvExtension_3560_, 2);
v___x_3563_ = lean_box(1);
v___x_3564_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_3565_ = lean_box(0);
v___x_3566_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3564_, v_toEnvExtension_3560_, v_env_3558_, v_asyncMode_3562_, v___x_3565_);
v_importedEntries_3567_ = lean_ctor_get(v___x_3566_, 0);
lean_inc_ref(v_importedEntries_3567_);
lean_dec(v___x_3566_);
v___x_3568_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3563_, v___x_3559_, v_env_3558_, v_asyncMode_3562_, v___x_3565_);
lean_inc_ref(v_exportEntriesFn_3561_);
v___x_3569_ = lean_apply_2(v_exportEntriesFn_3561_, v_env_3558_, v___x_3568_);
v_exported_3570_ = lean_ctor_get(v___x_3569_, 0);
lean_inc(v_exported_3570_);
lean_dec_ref(v___x_3569_);
v___x_3571_ = lean_array_push(v_importedEntries_3567_, v_exported_3570_);
v_sz_3572_ = lean_array_size(v___x_3571_);
v___x_3573_ = ((size_t)0ULL);
v___x_3574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v___x_3571_, v_sz_3572_, v___x_3573_, v___x_3563_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_);
lean_dec_ref(v___x_3571_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3599_; 
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3577_ = v___x_3574_;
v_isShared_3578_ = v_isSharedCheck_3599_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3574_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3599_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3579_; lean_object* v_ext_3580_; lean_object* v_toEnvExtension_3581_; lean_object* v_asyncMode_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v_categories_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3579_ = l_Lean_Parser_parserExtension;
v_ext_3580_ = lean_ctor_get(v___x_3579_, 1);
v_toEnvExtension_3581_ = lean_ctor_get(v_ext_3580_, 0);
v_asyncMode_3582_ = lean_ctor_get(v_toEnvExtension_3581_, 2);
v___x_3583_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref(v_env_3558_);
v___x_3584_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3583_, v___x_3579_, v_env_3558_, v_asyncMode_3582_);
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
lean_del_object(v___x_3577_);
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
lean_closure_set(v___f_3594_, 0, v_env_3558_);
lean_closure_set(v___f_3594_, 1, v___x_3565_);
lean_closure_set(v___f_3594_, 2, v_a_3575_);
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
lean_dec(v_a_3575_);
lean_dec_ref(v_env_3558_);
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 0, v___x_3586_);
v___x_3597_ = v___x_3577_;
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
lean_dec_ref(v_env_3558_);
v_a_3600_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3602_ = v___x_3574_;
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3574_);
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
