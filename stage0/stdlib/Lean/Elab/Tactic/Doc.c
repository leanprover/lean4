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
uint8_t lean_bool_not(uint8_t);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Parser_Tactic_Doc_isTactic(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
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
uint64_t lean_uint64_of_nat(lean_object*);
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0;
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
v___x_26_ = lean_alloc_ctor(0, 10, 0);
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
lean_object* v___x_115_; lean_object* v_scopes_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v_opts_119_; lean_object* v___x_120_; uint8_t v___x_121_; uint8_t v___x_122_; 
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
v___x_122_ = lean_bool_not(v___x_121_);
if (v___x_122_ == 0)
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
else
{
lean_object* v___x_142_; 
lean_dec(v_macroStack_112_);
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v_msgData_111_);
return v___x_142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_143_, lean_object* v_macroStack_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(v_msgData_143_, v_macroStack_144_, v___y_145_);
lean_dec(v___y_145_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(lean_object* v_msg_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_Elab_Command_getRef___redArg(v___y_149_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_a_153_; lean_object* v_macroStack_154_; lean_object* v___x_155_; lean_object* v_a_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_167_; 
v_a_153_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_a_153_);
lean_dec_ref_known(v___x_152_, 1);
v_macroStack_154_ = lean_ctor_get(v___y_149_, 4);
v___x_155_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msg_148_, v___y_150_);
v_a_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_a_156_);
lean_dec_ref(v___x_155_);
v___x_157_ = l_Lean_Elab_getBetterRef(v_a_153_, v_macroStack_154_);
lean_dec(v_a_153_);
lean_inc(v_macroStack_154_);
v___x_158_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(v_a_156_, v_macroStack_154_, v___y_150_);
v_a_159_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_167_ == 0)
{
v___x_161_ = v___x_158_;
v_isShared_162_ = v_isSharedCheck_167_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_158_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_167_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_165_; 
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_157_);
lean_ctor_set(v___x_163_, 1, v_a_159_);
if (v_isShared_162_ == 0)
{
lean_ctor_set_tag(v___x_161_, 1);
lean_ctor_set(v___x_161_, 0, v___x_163_);
v___x_165_ = v___x_161_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_163_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
else
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
lean_dec_ref(v_msg_148_);
v_a_168_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_175_ == 0)
{
v___x_170_ = v___x_152_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_152_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_168_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg___boxed(lean_object* v_msg_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v_msg_176_, v___y_177_, v___y_178_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(lean_object* v_ref_181_, lean_object* v_msg_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_Elab_Command_getRef___redArg(v___y_183_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; lean_object* v_fileName_188_; lean_object* v_fileMap_189_; lean_object* v_currRecDepth_190_; lean_object* v_cmdPos_191_; lean_object* v_macroStack_192_; lean_object* v_quotContext_x3f_193_; lean_object* v_currMacroScope_194_; lean_object* v_snap_x3f_195_; lean_object* v_cancelTk_x3f_196_; uint8_t v_suppressElabErrors_197_; lean_object* v_ref_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_a_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_a_187_);
lean_dec_ref_known(v___x_186_, 1);
v_fileName_188_ = lean_ctor_get(v___y_183_, 0);
v_fileMap_189_ = lean_ctor_get(v___y_183_, 1);
v_currRecDepth_190_ = lean_ctor_get(v___y_183_, 2);
v_cmdPos_191_ = lean_ctor_get(v___y_183_, 3);
v_macroStack_192_ = lean_ctor_get(v___y_183_, 4);
v_quotContext_x3f_193_ = lean_ctor_get(v___y_183_, 5);
v_currMacroScope_194_ = lean_ctor_get(v___y_183_, 6);
v_snap_x3f_195_ = lean_ctor_get(v___y_183_, 8);
v_cancelTk_x3f_196_ = lean_ctor_get(v___y_183_, 9);
v_suppressElabErrors_197_ = lean_ctor_get_uint8(v___y_183_, sizeof(void*)*10);
v_ref_198_ = l_Lean_replaceRef(v_ref_181_, v_a_187_);
lean_dec(v_a_187_);
lean_inc(v_cancelTk_x3f_196_);
lean_inc(v_snap_x3f_195_);
lean_inc(v_currMacroScope_194_);
lean_inc(v_quotContext_x3f_193_);
lean_inc(v_macroStack_192_);
lean_inc(v_cmdPos_191_);
lean_inc(v_currRecDepth_190_);
lean_inc_ref(v_fileMap_189_);
lean_inc_ref(v_fileName_188_);
v___x_199_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_199_, 0, v_fileName_188_);
lean_ctor_set(v___x_199_, 1, v_fileMap_189_);
lean_ctor_set(v___x_199_, 2, v_currRecDepth_190_);
lean_ctor_set(v___x_199_, 3, v_cmdPos_191_);
lean_ctor_set(v___x_199_, 4, v_macroStack_192_);
lean_ctor_set(v___x_199_, 5, v_quotContext_x3f_193_);
lean_ctor_set(v___x_199_, 6, v_currMacroScope_194_);
lean_ctor_set(v___x_199_, 7, v_ref_198_);
lean_ctor_set(v___x_199_, 8, v_snap_x3f_195_);
lean_ctor_set(v___x_199_, 9, v_cancelTk_x3f_196_);
lean_ctor_set_uint8(v___x_199_, sizeof(void*)*10, v_suppressElabErrors_197_);
v___x_200_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v_msg_182_, v___x_199_, v___y_184_);
lean_dec_ref_known(v___x_199_, 10);
return v___x_200_;
}
else
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
lean_dec_ref(v_msg_182_);
v_a_201_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_186_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_186_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg___boxed(lean_object* v_ref_209_, lean_object* v_msg_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_ref_209_, v_msg_210_, v___y_211_, v___y_212_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v_ref_209_);
return v_res_214_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5));
v___x_226_ = l_Lean_stringToMessageData(v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11));
v___x_238_ = l_Lean_stringToMessageData(v___x_237_);
return v___x_238_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13));
v___x_241_ = l_Lean_stringToMessageData(v___x_240_);
return v___x_241_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15));
v___x_244_ = l_Lean_stringToMessageData(v___x_243_);
return v___x_244_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__17));
v___x_247_ = l_Lean_stringToMessageData(v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension(lean_object* v_x_248_, lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_252_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4));
lean_inc(v_x_248_);
v___x_253_ = l_Lean_Syntax_isOfKind(v_x_248_, v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v_x_248_);
v___x_254_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_255_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_254_, v_a_249_, v_a_250_);
return v___x_255_;
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = l_Lean_Syntax_getArg(v_x_248_, v___x_256_);
lean_inc(v___x_257_);
v___x_258_ = l_Lean_Syntax_matchesNull(v___x_257_, v___x_256_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_257_);
v___x_260_ = l_Lean_Syntax_matchesNull(v___x_257_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; 
lean_dec(v___x_257_);
lean_dec(v_x_248_);
v___x_261_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_262_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_261_, v_a_249_, v_a_250_);
return v___x_262_;
}
else
{
lean_object* v_docs_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v_docs_263_ = l_Lean_Syntax_getArg(v___x_257_, v___x_256_);
lean_dec(v___x_257_);
v___x_264_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8));
lean_inc(v_docs_263_);
v___x_265_ = l_Lean_Syntax_isOfKind(v_docs_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; 
lean_dec(v_docs_263_);
lean_dec(v_x_248_);
v___x_266_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_267_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_266_, v_a_249_, v_a_250_);
return v___x_267_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_268_ = lean_unsigned_to_nat(2u);
v___x_269_ = l_Lean_Syntax_getArg(v_x_248_, v___x_268_);
lean_dec(v_x_248_);
v___x_270_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10));
lean_inc(v___x_269_);
v___x_271_ = l_Lean_Syntax_isOfKind(v___x_269_, v___x_270_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; 
lean_dec(v___x_269_);
lean_dec(v_docs_263_);
v___x_272_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_273_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_272_, v_a_249_, v_a_250_);
return v___x_273_;
}
else
{
lean_object* v___x_274_; lean_object* v___f_275_; lean_object* v___x_276_; 
v___x_274_ = lean_box(0);
lean_inc(v___x_269_);
v___f_275_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed), 9, 2);
lean_closure_set(v___f_275_, 0, v___x_269_);
lean_closure_set(v___f_275_, 1, v___x_274_);
v___x_276_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_275_, v_a_249_, v_a_250_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_340_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_340_ == 0)
{
v___x_279_ = v___x_276_;
v_isShared_280_ = v_isSharedCheck_340_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_276_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_340_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___y_282_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___x_327_; lean_object* v_env_328_; lean_object* v___x_329_; 
v___x_327_ = lean_st_ref_get(v_a_250_);
v_env_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc_ref(v_env_328_);
lean_dec(v___x_327_);
lean_inc(v_a_277_);
v___x_329_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_328_, v_a_277_);
if (lean_obj_tag(v___x_329_) == 1)
{
lean_object* v_val_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
lean_del_object(v___x_279_);
lean_dec(v_docs_263_);
v_val_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_val_330_);
lean_dec_ref_known(v___x_329_, 1);
v___x_331_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_332_ = l_Lean_MessageData_ofConstName(v_a_277_, v___x_258_);
v___x_333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_331_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
v___x_334_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16);
v___x_335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_333_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = l_Lean_MessageData_ofConstName(v_val_330_, v___x_258_);
v___x_337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_335_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___x_331_);
v___x_339_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v___x_269_, v___x_338_, v_a_249_, v_a_250_);
lean_dec(v___x_269_);
return v___x_339_;
}
else
{
lean_dec(v___x_329_);
v___y_315_ = v_a_249_;
v___y_316_ = v_a_250_;
goto v___jp_314_;
}
v___jp_281_:
{
lean_object* v___x_283_; lean_object* v_env_284_; lean_object* v_messages_285_; lean_object* v_scopes_286_; lean_object* v_usedQuotCtxts_287_; lean_object* v_nextMacroScope_288_; lean_object* v_maxRecDepth_289_; lean_object* v_ngen_290_; lean_object* v_auxDeclNGen_291_; lean_object* v_infoState_292_; lean_object* v_traceState_293_; lean_object* v_snapshotTasks_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_313_; 
v___x_283_ = lean_st_ref_take(v___y_282_);
v_env_284_ = lean_ctor_get(v___x_283_, 0);
v_messages_285_ = lean_ctor_get(v___x_283_, 1);
v_scopes_286_ = lean_ctor_get(v___x_283_, 2);
v_usedQuotCtxts_287_ = lean_ctor_get(v___x_283_, 3);
v_nextMacroScope_288_ = lean_ctor_get(v___x_283_, 4);
v_maxRecDepth_289_ = lean_ctor_get(v___x_283_, 5);
v_ngen_290_ = lean_ctor_get(v___x_283_, 6);
v_auxDeclNGen_291_ = lean_ctor_get(v___x_283_, 7);
v_infoState_292_ = lean_ctor_get(v___x_283_, 8);
v_traceState_293_ = lean_ctor_get(v___x_283_, 9);
v_snapshotTasks_294_ = lean_ctor_get(v___x_283_, 10);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_313_ == 0)
{
v___x_296_ = v___x_283_;
v_isShared_297_ = v_isSharedCheck_313_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_snapshotTasks_294_);
lean_inc(v_traceState_293_);
lean_inc(v_infoState_292_);
lean_inc(v_auxDeclNGen_291_);
lean_inc(v_ngen_290_);
lean_inc(v_maxRecDepth_289_);
lean_inc(v_nextMacroScope_288_);
lean_inc(v_usedQuotCtxts_287_);
lean_inc(v_scopes_286_);
lean_inc(v_messages_285_);
lean_inc(v_env_284_);
lean_dec(v___x_283_);
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
v___x_301_ = l_Lean_TSyntax_getDocString(v_docs_263_);
lean_dec(v_docs_263_);
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v_a_277_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = lean_box(0);
v___x_304_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_298_, v_env_284_, v___x_302_, v_asyncMode_300_, v___x_303_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_304_);
v___x_306_ = v___x_296_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_messages_285_);
lean_ctor_set(v_reuseFailAlloc_312_, 2, v_scopes_286_);
lean_ctor_set(v_reuseFailAlloc_312_, 3, v_usedQuotCtxts_287_);
lean_ctor_set(v_reuseFailAlloc_312_, 4, v_nextMacroScope_288_);
lean_ctor_set(v_reuseFailAlloc_312_, 5, v_maxRecDepth_289_);
lean_ctor_set(v_reuseFailAlloc_312_, 6, v_ngen_290_);
lean_ctor_set(v_reuseFailAlloc_312_, 7, v_auxDeclNGen_291_);
lean_ctor_set(v_reuseFailAlloc_312_, 8, v_infoState_292_);
lean_ctor_set(v_reuseFailAlloc_312_, 9, v_traceState_293_);
lean_ctor_set(v_reuseFailAlloc_312_, 10, v_snapshotTasks_294_);
v___x_306_ = v_reuseFailAlloc_312_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v___x_307_ = lean_st_ref_set(v___y_282_, v___x_306_);
v___x_308_ = lean_box(0);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_308_);
v___x_310_ = v___x_279_;
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
lean_object* v___x_317_; lean_object* v_env_318_; uint8_t v___x_319_; uint8_t v___x_320_; 
v___x_317_ = lean_st_ref_get(v___y_316_);
v_env_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc_ref(v_env_318_);
lean_dec(v___x_317_);
v___x_319_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_318_, v_a_277_);
v___x_320_ = lean_bool_not(v___x_319_);
if (v___x_320_ == 0)
{
lean_dec(v___x_269_);
v___y_282_ = v___y_316_;
goto v___jp_281_;
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
lean_del_object(v___x_279_);
lean_dec(v_docs_263_);
v___x_321_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_322_ = l_Lean_MessageData_ofConstName(v_a_277_, v___x_258_);
v___x_323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_321_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14);
v___x_325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_323_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v___x_269_, v___x_325_, v___y_315_, v___y_316_);
lean_dec(v___x_269_);
return v___x_326_;
}
}
}
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_dec(v___x_269_);
lean_dec(v_docs_263_);
v_a_341_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_276_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_276_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_349_; lean_object* v_cmd_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
lean_dec(v___x_257_);
v___x_349_ = lean_unsigned_to_nat(1u);
v_cmd_350_ = l_Lean_Syntax_getArg(v_x_248_, v___x_349_);
lean_dec(v_x_248_);
v___x_351_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18);
v___x_352_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_cmd_350_, v___x_351_, v_a_249_, v_a_250_);
lean_dec(v_cmd_350_);
return v___x_352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed(lean_object* v_x_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension(v_x_353_, v_a_354_, v_a_355_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(lean_object* v_msgData_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msgData_358_, v___y_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___boxed(lean_object* v_msgData_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(v_msgData_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(lean_object* v_00_u03b1_368_, lean_object* v_msg_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v_msg_369_, v___y_370_, v___y_371_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___boxed(lean_object* v_00_u03b1_374_, lean_object* v_msg_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(v_00_u03b1_374_, v_msg_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(lean_object* v_00_u03b1_380_, lean_object* v_ref_381_, lean_object* v_msg_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_ref_381_, v_msg_382_, v___y_383_, v___y_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___boxed(lean_object* v_00_u03b1_387_, lean_object* v_ref_388_, lean_object* v_msg_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(v_00_u03b1_387_, v_ref_388_, v_msg_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v_ref_388_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(lean_object* v_msgData_394_, lean_object* v_macroStack_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(v_msgData_394_, v_macroStack_395_, v___y_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___boxed(lean_object* v_msgData_400_, lean_object* v_macroStack_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(v_msgData_400_, v_macroStack_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1(){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_417_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_418_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4));
v___x_419_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_420_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed), 4, 0);
v___x_421_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_417_, v___x_418_, v___x_419_, v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3(){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_450_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_451_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6));
v___x_452_ = l_Lean_addBuiltinDeclarationRanges(v___x_450_, v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
return v_res_454_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0));
v___x_457_ = l_Lean_stringToMessageData(v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(lean_object* v_stx_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_val_470_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_unsigned_to_nat(1u);
v___x_478_ = l_Lean_Syntax_getArg(v_stx_459_, v___x_477_);
switch(lean_obj_tag(v___x_478_))
{
case 2:
{
lean_object* v_val_479_; 
lean_dec(v_stx_459_);
v_val_479_ = lean_ctor_get(v___x_478_, 1);
lean_inc_ref(v_val_479_);
lean_dec_ref_known(v___x_478_, 2);
v_val_470_ = v_val_479_;
goto v___jp_469_;
}
case 1:
{
lean_object* v_kind_480_; 
v_kind_480_ = lean_ctor_get(v___x_478_, 1);
lean_inc(v_kind_480_);
if (lean_obj_tag(v_kind_480_) == 1)
{
lean_object* v_pre_481_; 
v_pre_481_ = lean_ctor_get(v_kind_480_, 0);
lean_inc(v_pre_481_);
if (lean_obj_tag(v_pre_481_) == 1)
{
lean_object* v_pre_482_; 
v_pre_482_ = lean_ctor_get(v_pre_481_, 0);
lean_inc(v_pre_482_);
if (lean_obj_tag(v_pre_482_) == 1)
{
lean_object* v_pre_483_; 
v_pre_483_ = lean_ctor_get(v_pre_482_, 0);
lean_inc(v_pre_483_);
if (lean_obj_tag(v_pre_483_) == 1)
{
lean_object* v_pre_484_; 
v_pre_484_ = lean_ctor_get(v_pre_483_, 0);
if (lean_obj_tag(v_pre_484_) == 0)
{
lean_object* v_str_485_; lean_object* v_str_486_; lean_object* v_str_487_; lean_object* v_str_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
v_str_485_ = lean_ctor_get(v_kind_480_, 1);
lean_inc_ref(v_str_485_);
lean_dec_ref_known(v_kind_480_, 2);
v_str_486_ = lean_ctor_get(v_pre_481_, 1);
lean_inc_ref(v_str_486_);
lean_dec_ref_known(v_pre_481_, 2);
v_str_487_ = lean_ctor_get(v_pre_482_, 1);
lean_inc_ref(v_str_487_);
lean_dec_ref_known(v_pre_482_, 2);
v_str_488_ = lean_ctor_get(v_pre_483_, 1);
lean_inc_ref(v_str_488_);
lean_dec_ref_known(v_pre_483_, 2);
v___x_489_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0));
v___x_490_ = lean_string_dec_eq(v_str_488_, v___x_489_);
lean_dec_ref(v_str_488_);
if (v___x_490_ == 0)
{
lean_dec_ref(v_str_487_);
lean_dec_ref(v_str_486_);
lean_dec_ref(v_str_485_);
lean_dec_ref_known(v___x_478_, 3);
goto v___jp_463_;
}
else
{
lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_491_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1));
v___x_492_ = lean_string_dec_eq(v_str_487_, v___x_491_);
lean_dec_ref(v_str_487_);
if (v___x_492_ == 0)
{
lean_dec_ref(v_str_486_);
lean_dec_ref(v_str_485_);
lean_dec_ref_known(v___x_478_, 3);
goto v___jp_463_;
}
else
{
lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_493_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2));
v___x_494_ = lean_string_dec_eq(v_str_486_, v___x_493_);
lean_dec_ref(v_str_486_);
if (v___x_494_ == 0)
{
lean_dec_ref(v_str_485_);
lean_dec_ref_known(v___x_478_, 3);
goto v___jp_463_;
}
else
{
lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_495_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2));
v___x_496_ = lean_string_dec_eq(v_str_485_, v___x_495_);
lean_dec_ref(v_str_485_);
if (v___x_496_ == 0)
{
lean_dec_ref_known(v___x_478_, 3);
goto v___jp_463_;
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = l_Lean_Syntax_getArg(v___x_478_, v___x_497_);
lean_dec_ref_known(v___x_478_, 3);
if (lean_obj_tag(v___x_498_) == 2)
{
lean_object* v_val_499_; 
lean_dec(v_stx_459_);
v_val_499_ = lean_ctor_get(v___x_498_, 1);
lean_inc_ref(v_val_499_);
lean_dec_ref_known(v___x_498_, 2);
v_val_470_ = v_val_499_;
goto v___jp_469_;
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec(v___x_498_);
v___x_500_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1);
lean_inc(v_stx_459_);
v___x_501_ = l_Lean_MessageData_ofSyntax(v_stx_459_);
v___x_502_ = l_Lean_indentD(v___x_501_);
v___x_503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_500_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
v___x_504_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_stx_459_, v___x_503_, v___y_460_, v___y_461_);
lean_dec(v_stx_459_);
return v___x_504_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_483_, 2);
lean_dec_ref_known(v_pre_482_, 2);
lean_dec_ref_known(v_pre_481_, 2);
lean_dec_ref_known(v_kind_480_, 2);
lean_dec_ref_known(v___x_478_, 3);
goto v___jp_463_;
}
}
else
{
lean_dec(v_pre_483_);
lean_dec_ref_known(v_pre_482_, 2);
lean_dec_ref_known(v_pre_481_, 2);
lean_dec_ref_known(v_kind_480_, 2);
lean_dec_ref_known(v___x_478_, 3);
goto v___jp_463_;
}
}
else
{
lean_dec(v_pre_482_);
lean_dec_ref_known(v_pre_481_, 2);
lean_dec_ref_known(v_kind_480_, 2);
lean_dec_ref_known(v___x_478_, 3);
goto v___jp_463_;
}
}
else
{
lean_dec_ref_known(v_kind_480_, 2);
lean_dec(v_pre_481_);
lean_dec_ref_known(v___x_478_, 3);
goto v___jp_463_;
}
}
else
{
lean_dec(v_kind_480_);
lean_dec_ref_known(v___x_478_, 3);
goto v___jp_463_;
}
}
default: 
{
lean_dec(v___x_478_);
goto v___jp_463_;
}
}
v___jp_463_:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_464_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1);
lean_inc(v_stx_459_);
v___x_465_ = l_Lean_MessageData_ofSyntax(v_stx_459_);
v___x_466_ = l_Lean_indentD(v___x_465_);
v___x_467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_464_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_stx_459_, v___x_467_, v___y_460_, v___y_461_);
lean_dec(v_stx_459_);
return v___x_468_;
}
v___jp_469_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = lean_string_utf8_byte_size(v_val_470_);
v___x_473_ = lean_unsigned_to_nat(2u);
v___x_474_ = lean_nat_sub(v___x_472_, v___x_473_);
v___x_475_ = lean_string_utf8_extract(v_val_470_, v___x_471_, v___x_474_);
lean_dec(v___x_474_);
lean_dec_ref(v_val_470_);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___boxed(lean_object* v_stx_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(v_stx_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
return v_res_509_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0));
v___x_512_ = l_Lean_stringToMessageData(v___x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(lean_object* v_x_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v_a_530_; lean_object* v_doc_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_597_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
lean_inc(v_x_522_);
v___x_598_ = l_Lean_Syntax_isOfKind(v_x_522_, v___x_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; 
lean_dec(v_x_522_);
v___x_599_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_600_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_599_, v_a_523_, v_a_524_);
return v___x_600_;
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_601_ = lean_unsigned_to_nat(0u);
v___x_602_ = l_Lean_Syntax_getArg(v_x_522_, v___x_601_);
v___x_603_ = l_Lean_Syntax_isNone(v___x_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_602_);
v___x_605_ = l_Lean_Syntax_matchesNull(v___x_602_, v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; 
lean_dec(v___x_602_);
lean_dec(v_x_522_);
v___x_606_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_607_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_606_, v_a_523_, v_a_524_);
return v___x_607_;
}
else
{
lean_object* v_doc_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v_doc_608_ = l_Lean_Syntax_getArg(v___x_602_, v___x_601_);
lean_dec(v___x_602_);
v___x_609_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8));
lean_inc(v_doc_608_);
v___x_610_ = l_Lean_Syntax_isOfKind(v_doc_608_, v___x_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; 
lean_dec(v_doc_608_);
lean_dec(v_x_522_);
v___x_611_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_612_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_611_, v_a_523_, v_a_524_);
return v___x_612_;
}
else
{
lean_object* v___x_613_; 
v___x_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_613_, 0, v_doc_608_);
v_doc_563_ = v___x_613_;
v___y_564_ = v_a_523_;
v___y_565_ = v_a_524_;
goto v___jp_562_;
}
}
}
else
{
lean_object* v___x_614_; 
lean_dec(v___x_602_);
v___x_614_ = lean_box(0);
v_doc_563_ = v___x_614_;
v___y_564_ = v_a_523_;
v___y_565_ = v_a_524_;
goto v___jp_562_;
}
}
v___jp_526_:
{
lean_object* v___x_531_; lean_object* v_env_532_; lean_object* v_messages_533_; lean_object* v_scopes_534_; lean_object* v_usedQuotCtxts_535_; lean_object* v_nextMacroScope_536_; lean_object* v_maxRecDepth_537_; lean_object* v_ngen_538_; lean_object* v_auxDeclNGen_539_; lean_object* v_infoState_540_; lean_object* v_traceState_541_; lean_object* v_snapshotTasks_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_561_; 
v___x_531_ = lean_st_ref_take(v___y_528_);
v_env_532_ = lean_ctor_get(v___x_531_, 0);
v_messages_533_ = lean_ctor_get(v___x_531_, 1);
v_scopes_534_ = lean_ctor_get(v___x_531_, 2);
v_usedQuotCtxts_535_ = lean_ctor_get(v___x_531_, 3);
v_nextMacroScope_536_ = lean_ctor_get(v___x_531_, 4);
v_maxRecDepth_537_ = lean_ctor_get(v___x_531_, 5);
v_ngen_538_ = lean_ctor_get(v___x_531_, 6);
v_auxDeclNGen_539_ = lean_ctor_get(v___x_531_, 7);
v_infoState_540_ = lean_ctor_get(v___x_531_, 8);
v_traceState_541_ = lean_ctor_get(v___x_531_, 9);
v_snapshotTasks_542_ = lean_ctor_get(v___x_531_, 10);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_561_ == 0)
{
v___x_544_ = v___x_531_;
v_isShared_545_ = v_isSharedCheck_561_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_snapshotTasks_542_);
lean_inc(v_traceState_541_);
lean_inc(v_infoState_540_);
lean_inc(v_auxDeclNGen_539_);
lean_inc(v_ngen_538_);
lean_inc(v_maxRecDepth_537_);
lean_inc(v_nextMacroScope_536_);
lean_inc(v_usedQuotCtxts_535_);
lean_inc(v_scopes_534_);
lean_inc(v_messages_533_);
lean_inc(v_env_532_);
lean_dec(v___x_531_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_561_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v_toEnvExtension_547_; lean_object* v_asyncMode_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_546_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_547_ = lean_ctor_get(v___x_546_, 0);
v_asyncMode_548_ = lean_ctor_get(v_toEnvExtension_547_, 2);
v___x_549_ = l_Lean_TSyntax_getId(v___y_529_);
lean_dec(v___y_529_);
v___x_550_ = l_Lean_TSyntax_getString(v___y_527_);
lean_dec(v___y_527_);
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set(v___x_551_, 1, v_a_530_);
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_549_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = lean_box(0);
v___x_554_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_546_, v_env_532_, v___x_552_, v_asyncMode_548_, v___x_553_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_554_);
v___x_556_ = v___x_544_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_messages_533_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v_scopes_534_);
lean_ctor_set(v_reuseFailAlloc_560_, 3, v_usedQuotCtxts_535_);
lean_ctor_set(v_reuseFailAlloc_560_, 4, v_nextMacroScope_536_);
lean_ctor_set(v_reuseFailAlloc_560_, 5, v_maxRecDepth_537_);
lean_ctor_set(v_reuseFailAlloc_560_, 6, v_ngen_538_);
lean_ctor_set(v_reuseFailAlloc_560_, 7, v_auxDeclNGen_539_);
lean_ctor_set(v_reuseFailAlloc_560_, 8, v_infoState_540_);
lean_ctor_set(v_reuseFailAlloc_560_, 9, v_traceState_541_);
lean_ctor_set(v_reuseFailAlloc_560_, 10, v_snapshotTasks_542_);
v___x_556_ = v_reuseFailAlloc_560_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_557_ = lean_st_ref_set(v___y_528_, v___x_556_);
v___x_558_ = lean_box(0);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
return v___x_559_;
}
}
}
v___jp_562_:
{
lean_object* v___x_566_; lean_object* v_tag_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_566_ = lean_unsigned_to_nat(2u);
v_tag_567_ = l_Lean_Syntax_getArg(v_x_522_, v___x_566_);
v___x_568_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10));
lean_inc(v_tag_567_);
v___x_569_ = l_Lean_Syntax_isOfKind(v_tag_567_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec(v_tag_567_);
lean_dec(v_doc_563_);
lean_dec(v_x_522_);
v___x_570_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_571_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_570_, v___y_564_, v___y_565_);
return v___x_571_;
}
else
{
lean_object* v___x_572_; lean_object* v_user_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_572_ = lean_unsigned_to_nat(3u);
v_user_573_ = l_Lean_Syntax_getArg(v_x_522_, v___x_572_);
lean_dec(v_x_522_);
v___x_574_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3));
lean_inc(v_user_573_);
v___x_575_ = l_Lean_Syntax_isOfKind(v_user_573_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v_user_573_);
lean_dec(v_tag_567_);
lean_dec(v_doc_563_);
v___x_576_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_577_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_576_, v___y_564_, v___y_565_);
return v___x_577_;
}
else
{
if (lean_obj_tag(v_doc_563_) == 0)
{
lean_object* v___x_578_; 
v___x_578_ = lean_box(0);
v___y_527_ = v_user_573_;
v___y_528_ = v___y_565_;
v___y_529_ = v_tag_567_;
v_a_530_ = v___x_578_;
goto v___jp_526_;
}
else
{
lean_object* v_val_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_596_; 
v_val_579_ = lean_ctor_get(v_doc_563_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v_doc_563_);
if (v_isSharedCheck_596_ == 0)
{
v___x_581_ = v_doc_563_;
v_isShared_582_ = v_isSharedCheck_596_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_val_579_);
lean_dec(v_doc_563_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_596_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(v_val_579_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_586_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
lean_dec_ref_known(v___x_583_, 1);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v_a_584_);
v___x_586_ = v___x_581_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
v___y_527_ = v_user_573_;
v___y_528_ = v___y_565_;
v___y_529_ = v_tag_567_;
v_a_530_ = v___x_586_;
goto v___jp_526_;
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_del_object(v___x_581_);
lean_dec(v_user_573_);
lean_dec(v_tag_567_);
v_a_588_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_583_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_583_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed(lean_object* v_x_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(v_x_615_, v_a_616_, v_a_617_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1(){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_628_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_629_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
v___x_630_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_631_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed), 4, 0);
v___x_632_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_628_, v___x_629_, v___x_630_, v___x_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3(){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_661_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_662_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6));
v___x_663_ = l_Lean_addBuiltinDeclarationRanges(v___x_661_, v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object* v_a_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(lean_object* v___x_666_, lean_object* v_x_667_){
_start:
{
if (lean_obj_tag(v_x_667_) == 0)
{
lean_object* v___x_668_; 
v___x_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_666_);
return v___x_668_;
}
else
{
lean_dec_ref(v___x_666_);
lean_inc_ref(v_x_667_);
return v_x_667_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_669_, lean_object* v_x_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_669_, v_x_670_);
lean_dec(v_x_670_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(lean_object* v___x_672_, lean_object* v_k_673_, lean_object* v_t_674_){
_start:
{
if (lean_obj_tag(v_t_674_) == 0)
{
lean_object* v_size_675_; lean_object* v_k_676_; lean_object* v_v_677_; lean_object* v_l_678_; lean_object* v_r_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_1005_; 
v_size_675_ = lean_ctor_get(v_t_674_, 0);
v_k_676_ = lean_ctor_get(v_t_674_, 1);
v_v_677_ = lean_ctor_get(v_t_674_, 2);
v_l_678_ = lean_ctor_get(v_t_674_, 3);
v_r_679_ = lean_ctor_get(v_t_674_, 4);
v_isSharedCheck_1005_ = !lean_is_exclusive(v_t_674_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_681_ = v_t_674_;
v_isShared_682_ = v_isSharedCheck_1005_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_r_679_);
lean_inc(v_l_678_);
lean_inc(v_v_677_);
lean_inc(v_k_676_);
lean_inc(v_size_675_);
lean_dec(v_t_674_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_1005_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
uint8_t v___x_683_; 
v___x_683_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_673_, v_k_676_);
switch(v___x_683_)
{
case 0:
{
lean_object* v_impl_684_; lean_object* v___x_685_; 
lean_del_object(v___x_681_);
lean_dec(v_size_675_);
v_impl_684_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_672_, v_k_673_, v_l_678_);
v___x_685_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_676_, v_v_677_, v_impl_684_, v_r_679_);
return v___x_685_;
}
case 1:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
lean_dec(v_k_676_);
v___x_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_686_, 0, v_v_677_);
v___x_687_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_672_, v___x_686_);
lean_dec_ref_known(v___x_686_, 1);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_del_object(v___x_681_);
lean_dec(v_size_675_);
lean_dec(v_k_673_);
if (lean_obj_tag(v_l_678_) == 0)
{
if (lean_obj_tag(v_r_679_) == 0)
{
lean_object* v_size_688_; lean_object* v_k_689_; lean_object* v_v_690_; lean_object* v_l_691_; lean_object* v_r_692_; lean_object* v_size_693_; lean_object* v_k_694_; lean_object* v_v_695_; lean_object* v_l_696_; lean_object* v_r_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v_size_688_ = lean_ctor_get(v_l_678_, 0);
v_k_689_ = lean_ctor_get(v_l_678_, 1);
v_v_690_ = lean_ctor_get(v_l_678_, 2);
v_l_691_ = lean_ctor_get(v_l_678_, 3);
v_r_692_ = lean_ctor_get(v_l_678_, 4);
lean_inc(v_r_692_);
v_size_693_ = lean_ctor_get(v_r_679_, 0);
v_k_694_ = lean_ctor_get(v_r_679_, 1);
v_v_695_ = lean_ctor_get(v_r_679_, 2);
v_l_696_ = lean_ctor_get(v_r_679_, 3);
lean_inc(v_l_696_);
v_r_697_ = lean_ctor_get(v_r_679_, 4);
v___x_698_ = lean_unsigned_to_nat(1u);
v___x_699_ = lean_nat_dec_lt(v_size_688_, v_size_693_);
if (v___x_699_ == 0)
{
lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_835_; 
lean_inc(v_l_691_);
lean_inc(v_v_690_);
lean_inc(v_k_689_);
v_isSharedCheck_835_ = !lean_is_exclusive(v_l_678_);
if (v_isSharedCheck_835_ == 0)
{
lean_object* v_unused_836_; lean_object* v_unused_837_; lean_object* v_unused_838_; lean_object* v_unused_839_; lean_object* v_unused_840_; 
v_unused_836_ = lean_ctor_get(v_l_678_, 4);
lean_dec(v_unused_836_);
v_unused_837_ = lean_ctor_get(v_l_678_, 3);
lean_dec(v_unused_837_);
v_unused_838_ = lean_ctor_get(v_l_678_, 2);
lean_dec(v_unused_838_);
v_unused_839_ = lean_ctor_get(v_l_678_, 1);
lean_dec(v_unused_839_);
v_unused_840_ = lean_ctor_get(v_l_678_, 0);
lean_dec(v_unused_840_);
v___x_701_ = v_l_678_;
v_isShared_702_ = v_isSharedCheck_835_;
goto v_resetjp_700_;
}
else
{
lean_dec(v_l_678_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_835_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v_tree_704_; 
v___x_703_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_689_, v_v_690_, v_l_691_, v_r_692_);
v_tree_704_ = lean_ctor_get(v___x_703_, 2);
lean_inc(v_tree_704_);
if (lean_obj_tag(v_tree_704_) == 0)
{
lean_object* v_k_705_; lean_object* v_v_706_; lean_object* v_size_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v_k_705_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_k_705_);
v_v_706_ = lean_ctor_get(v___x_703_, 1);
lean_inc(v_v_706_);
lean_dec_ref(v___x_703_);
v_size_707_ = lean_ctor_get(v_tree_704_, 0);
v___x_708_ = lean_unsigned_to_nat(3u);
v___x_709_ = lean_nat_mul(v___x_708_, v_size_707_);
v___x_710_ = lean_nat_dec_lt(v___x_709_, v_size_693_);
lean_dec(v___x_709_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_714_; 
lean_dec(v_l_696_);
v___x_711_ = lean_nat_add(v___x_698_, v_size_707_);
v___x_712_ = lean_nat_add(v___x_711_, v_size_693_);
lean_dec(v___x_711_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 4, v_r_679_);
lean_ctor_set(v___x_701_, 3, v_tree_704_);
lean_ctor_set(v___x_701_, 2, v_v_706_);
lean_ctor_set(v___x_701_, 1, v_k_705_);
lean_ctor_set(v___x_701_, 0, v___x_712_);
v___x_714_ = v___x_701_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_k_705_);
lean_ctor_set(v_reuseFailAlloc_715_, 2, v_v_706_);
lean_ctor_set(v_reuseFailAlloc_715_, 3, v_tree_704_);
lean_ctor_set(v_reuseFailAlloc_715_, 4, v_r_679_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
else
{
lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_770_; 
lean_inc(v_r_697_);
lean_inc(v_v_695_);
lean_inc(v_k_694_);
lean_inc(v_size_693_);
v_isSharedCheck_770_ = !lean_is_exclusive(v_r_679_);
if (v_isSharedCheck_770_ == 0)
{
lean_object* v_unused_771_; lean_object* v_unused_772_; lean_object* v_unused_773_; lean_object* v_unused_774_; lean_object* v_unused_775_; 
v_unused_771_ = lean_ctor_get(v_r_679_, 4);
lean_dec(v_unused_771_);
v_unused_772_ = lean_ctor_get(v_r_679_, 3);
lean_dec(v_unused_772_);
v_unused_773_ = lean_ctor_get(v_r_679_, 2);
lean_dec(v_unused_773_);
v_unused_774_ = lean_ctor_get(v_r_679_, 1);
lean_dec(v_unused_774_);
v_unused_775_ = lean_ctor_get(v_r_679_, 0);
lean_dec(v_unused_775_);
v___x_717_ = v_r_679_;
v_isShared_718_ = v_isSharedCheck_770_;
goto v_resetjp_716_;
}
else
{
lean_dec(v_r_679_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_770_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v_size_719_; lean_object* v_k_720_; lean_object* v_v_721_; lean_object* v_l_722_; lean_object* v_r_723_; lean_object* v_size_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v_size_719_ = lean_ctor_get(v_l_696_, 0);
v_k_720_ = lean_ctor_get(v_l_696_, 1);
v_v_721_ = lean_ctor_get(v_l_696_, 2);
v_l_722_ = lean_ctor_get(v_l_696_, 3);
v_r_723_ = lean_ctor_get(v_l_696_, 4);
v_size_724_ = lean_ctor_get(v_r_697_, 0);
v___x_725_ = lean_unsigned_to_nat(2u);
v___x_726_ = lean_nat_mul(v___x_725_, v_size_724_);
v___x_727_ = lean_nat_dec_lt(v_size_719_, v___x_726_);
lean_dec(v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_755_; 
lean_inc(v_r_723_);
lean_inc(v_l_722_);
lean_inc(v_v_721_);
lean_inc(v_k_720_);
v_isSharedCheck_755_ = !lean_is_exclusive(v_l_696_);
if (v_isSharedCheck_755_ == 0)
{
lean_object* v_unused_756_; lean_object* v_unused_757_; lean_object* v_unused_758_; lean_object* v_unused_759_; lean_object* v_unused_760_; 
v_unused_756_ = lean_ctor_get(v_l_696_, 4);
lean_dec(v_unused_756_);
v_unused_757_ = lean_ctor_get(v_l_696_, 3);
lean_dec(v_unused_757_);
v_unused_758_ = lean_ctor_get(v_l_696_, 2);
lean_dec(v_unused_758_);
v_unused_759_ = lean_ctor_get(v_l_696_, 1);
lean_dec(v_unused_759_);
v_unused_760_ = lean_ctor_get(v_l_696_, 0);
lean_dec(v_unused_760_);
v___x_729_ = v_l_696_;
v_isShared_730_ = v_isSharedCheck_755_;
goto v_resetjp_728_;
}
else
{
lean_dec(v_l_696_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_755_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_745_; 
v___x_731_ = lean_nat_add(v___x_698_, v_size_707_);
v___x_732_ = lean_nat_add(v___x_731_, v_size_693_);
lean_dec(v_size_693_);
if (lean_obj_tag(v_l_722_) == 0)
{
lean_object* v_size_753_; 
v_size_753_ = lean_ctor_get(v_l_722_, 0);
lean_inc(v_size_753_);
v___y_745_ = v_size_753_;
goto v___jp_744_;
}
else
{
lean_object* v___x_754_; 
v___x_754_ = lean_unsigned_to_nat(0u);
v___y_745_ = v___x_754_;
goto v___jp_744_;
}
v___jp_733_:
{
lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_737_ = lean_nat_add(v___y_734_, v___y_736_);
lean_dec(v___y_736_);
lean_dec(v___y_734_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 4, v_r_697_);
lean_ctor_set(v___x_729_, 3, v_r_723_);
lean_ctor_set(v___x_729_, 2, v_v_695_);
lean_ctor_set(v___x_729_, 1, v_k_694_);
lean_ctor_set(v___x_729_, 0, v___x_737_);
v___x_739_ = v___x_729_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_k_694_);
lean_ctor_set(v_reuseFailAlloc_743_, 2, v_v_695_);
lean_ctor_set(v_reuseFailAlloc_743_, 3, v_r_723_);
lean_ctor_set(v_reuseFailAlloc_743_, 4, v_r_697_);
v___x_739_ = v_reuseFailAlloc_743_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_object* v___x_741_; 
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 4, v___x_739_);
lean_ctor_set(v___x_717_, 3, v___y_735_);
lean_ctor_set(v___x_717_, 2, v_v_721_);
lean_ctor_set(v___x_717_, 1, v_k_720_);
lean_ctor_set(v___x_717_, 0, v___x_732_);
v___x_741_ = v___x_717_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_k_720_);
lean_ctor_set(v_reuseFailAlloc_742_, 2, v_v_721_);
lean_ctor_set(v_reuseFailAlloc_742_, 3, v___y_735_);
lean_ctor_set(v_reuseFailAlloc_742_, 4, v___x_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
v___jp_744_:
{
lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_746_ = lean_nat_add(v___x_731_, v___y_745_);
lean_dec(v___y_745_);
lean_dec(v___x_731_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 4, v_l_722_);
lean_ctor_set(v___x_701_, 3, v_tree_704_);
lean_ctor_set(v___x_701_, 2, v_v_706_);
lean_ctor_set(v___x_701_, 1, v_k_705_);
lean_ctor_set(v___x_701_, 0, v___x_746_);
v___x_748_ = v___x_701_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_k_705_);
lean_ctor_set(v_reuseFailAlloc_752_, 2, v_v_706_);
lean_ctor_set(v_reuseFailAlloc_752_, 3, v_tree_704_);
lean_ctor_set(v_reuseFailAlloc_752_, 4, v_l_722_);
v___x_748_ = v_reuseFailAlloc_752_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_749_; 
v___x_749_ = lean_nat_add(v___x_698_, v_size_724_);
if (lean_obj_tag(v_r_723_) == 0)
{
lean_object* v_size_750_; 
v_size_750_ = lean_ctor_get(v_r_723_, 0);
lean_inc(v_size_750_);
v___y_734_ = v___x_749_;
v___y_735_ = v___x_748_;
v___y_736_ = v_size_750_;
goto v___jp_733_;
}
else
{
lean_object* v___x_751_; 
v___x_751_ = lean_unsigned_to_nat(0u);
v___y_734_ = v___x_749_;
v___y_735_ = v___x_748_;
v___y_736_ = v___x_751_;
goto v___jp_733_;
}
}
}
}
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_761_ = lean_nat_add(v___x_698_, v_size_707_);
v___x_762_ = lean_nat_add(v___x_761_, v_size_693_);
lean_dec(v_size_693_);
v___x_763_ = lean_nat_add(v___x_761_, v_size_719_);
lean_dec(v___x_761_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 4, v_l_696_);
lean_ctor_set(v___x_717_, 3, v_tree_704_);
lean_ctor_set(v___x_717_, 2, v_v_706_);
lean_ctor_set(v___x_717_, 1, v_k_705_);
lean_ctor_set(v___x_717_, 0, v___x_763_);
v___x_765_ = v___x_717_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_k_705_);
lean_ctor_set(v_reuseFailAlloc_769_, 2, v_v_706_);
lean_ctor_set(v_reuseFailAlloc_769_, 3, v_tree_704_);
lean_ctor_set(v_reuseFailAlloc_769_, 4, v_l_696_);
v___x_765_ = v_reuseFailAlloc_769_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_767_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 4, v_r_697_);
lean_ctor_set(v___x_701_, 3, v___x_765_);
lean_ctor_set(v___x_701_, 2, v_v_695_);
lean_ctor_set(v___x_701_, 1, v_k_694_);
lean_ctor_set(v___x_701_, 0, v___x_762_);
v___x_767_ = v___x_701_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_k_694_);
lean_ctor_set(v_reuseFailAlloc_768_, 2, v_v_695_);
lean_ctor_set(v_reuseFailAlloc_768_, 3, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_768_, 4, v_r_697_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
}
else
{
lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_829_; 
lean_inc(v_r_697_);
lean_inc(v_v_695_);
lean_inc(v_k_694_);
lean_inc(v_size_693_);
v_isSharedCheck_829_ = !lean_is_exclusive(v_r_679_);
if (v_isSharedCheck_829_ == 0)
{
lean_object* v_unused_830_; lean_object* v_unused_831_; lean_object* v_unused_832_; lean_object* v_unused_833_; lean_object* v_unused_834_; 
v_unused_830_ = lean_ctor_get(v_r_679_, 4);
lean_dec(v_unused_830_);
v_unused_831_ = lean_ctor_get(v_r_679_, 3);
lean_dec(v_unused_831_);
v_unused_832_ = lean_ctor_get(v_r_679_, 2);
lean_dec(v_unused_832_);
v_unused_833_ = lean_ctor_get(v_r_679_, 1);
lean_dec(v_unused_833_);
v_unused_834_ = lean_ctor_get(v_r_679_, 0);
lean_dec(v_unused_834_);
v___x_777_ = v_r_679_;
v_isShared_778_ = v_isSharedCheck_829_;
goto v_resetjp_776_;
}
else
{
lean_dec(v_r_679_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_829_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
if (lean_obj_tag(v_l_696_) == 0)
{
if (lean_obj_tag(v_r_697_) == 0)
{
lean_object* v_k_779_; lean_object* v_v_780_; lean_object* v_size_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v_k_779_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_k_779_);
v_v_780_ = lean_ctor_get(v___x_703_, 1);
lean_inc(v_v_780_);
lean_dec_ref(v___x_703_);
v_size_781_ = lean_ctor_get(v_l_696_, 0);
v___x_782_ = lean_nat_add(v___x_698_, v_size_693_);
lean_dec(v_size_693_);
v___x_783_ = lean_nat_add(v___x_698_, v_size_781_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 4, v_l_696_);
lean_ctor_set(v___x_777_, 3, v_tree_704_);
lean_ctor_set(v___x_777_, 2, v_v_780_);
lean_ctor_set(v___x_777_, 1, v_k_779_);
lean_ctor_set(v___x_777_, 0, v___x_783_);
v___x_785_ = v___x_777_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_k_779_);
lean_ctor_set(v_reuseFailAlloc_789_, 2, v_v_780_);
lean_ctor_set(v_reuseFailAlloc_789_, 3, v_tree_704_);
lean_ctor_set(v_reuseFailAlloc_789_, 4, v_l_696_);
v___x_785_ = v_reuseFailAlloc_789_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_787_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 4, v_r_697_);
lean_ctor_set(v___x_701_, 3, v___x_785_);
lean_ctor_set(v___x_701_, 2, v_v_695_);
lean_ctor_set(v___x_701_, 1, v_k_694_);
lean_ctor_set(v___x_701_, 0, v___x_782_);
v___x_787_ = v___x_701_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_k_694_);
lean_ctor_set(v_reuseFailAlloc_788_, 2, v_v_695_);
lean_ctor_set(v_reuseFailAlloc_788_, 3, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_788_, 4, v_r_697_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
else
{
lean_object* v_k_790_; lean_object* v_v_791_; lean_object* v_k_792_; lean_object* v_v_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_807_; 
lean_dec(v_size_693_);
v_k_790_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_k_790_);
v_v_791_ = lean_ctor_get(v___x_703_, 1);
lean_inc(v_v_791_);
lean_dec_ref(v___x_703_);
v_k_792_ = lean_ctor_get(v_l_696_, 1);
v_v_793_ = lean_ctor_get(v_l_696_, 2);
v_isSharedCheck_807_ = !lean_is_exclusive(v_l_696_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; lean_object* v_unused_809_; lean_object* v_unused_810_; 
v_unused_808_ = lean_ctor_get(v_l_696_, 4);
lean_dec(v_unused_808_);
v_unused_809_ = lean_ctor_get(v_l_696_, 3);
lean_dec(v_unused_809_);
v_unused_810_ = lean_ctor_get(v_l_696_, 0);
lean_dec(v_unused_810_);
v___x_795_ = v_l_696_;
v_isShared_796_ = v_isSharedCheck_807_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_v_793_);
lean_inc(v_k_792_);
lean_dec(v_l_696_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_807_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = lean_unsigned_to_nat(3u);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 4, v_r_697_);
lean_ctor_set(v___x_795_, 3, v_r_697_);
lean_ctor_set(v___x_795_, 2, v_v_791_);
lean_ctor_set(v___x_795_, 1, v_k_790_);
lean_ctor_set(v___x_795_, 0, v___x_698_);
v___x_799_ = v___x_795_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_k_790_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v_v_791_);
lean_ctor_set(v_reuseFailAlloc_806_, 3, v_r_697_);
lean_ctor_set(v_reuseFailAlloc_806_, 4, v_r_697_);
v___x_799_ = v_reuseFailAlloc_806_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_801_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 3, v_r_697_);
lean_ctor_set(v___x_777_, 0, v___x_698_);
v___x_801_ = v___x_777_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_k_694_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v_v_695_);
lean_ctor_set(v_reuseFailAlloc_805_, 3, v_r_697_);
lean_ctor_set(v_reuseFailAlloc_805_, 4, v_r_697_);
v___x_801_ = v_reuseFailAlloc_805_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_803_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 4, v___x_801_);
lean_ctor_set(v___x_701_, 3, v___x_799_);
lean_ctor_set(v___x_701_, 2, v_v_793_);
lean_ctor_set(v___x_701_, 1, v_k_792_);
lean_ctor_set(v___x_701_, 0, v___x_797_);
v___x_803_ = v___x_701_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_k_792_);
lean_ctor_set(v_reuseFailAlloc_804_, 2, v_v_793_);
lean_ctor_set(v_reuseFailAlloc_804_, 3, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_804_, 4, v___x_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_697_) == 0)
{
lean_object* v_k_811_; lean_object* v_v_812_; lean_object* v___x_813_; lean_object* v___x_815_; 
lean_dec(v_size_693_);
v_k_811_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_k_811_);
v_v_812_ = lean_ctor_get(v___x_703_, 1);
lean_inc(v_v_812_);
lean_dec_ref(v___x_703_);
v___x_813_ = lean_unsigned_to_nat(3u);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 4, v_l_696_);
lean_ctor_set(v___x_777_, 2, v_v_812_);
lean_ctor_set(v___x_777_, 1, v_k_811_);
lean_ctor_set(v___x_777_, 0, v___x_698_);
v___x_815_ = v___x_777_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_k_811_);
lean_ctor_set(v_reuseFailAlloc_819_, 2, v_v_812_);
lean_ctor_set(v_reuseFailAlloc_819_, 3, v_l_696_);
lean_ctor_set(v_reuseFailAlloc_819_, 4, v_l_696_);
v___x_815_ = v_reuseFailAlloc_819_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_817_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 4, v_r_697_);
lean_ctor_set(v___x_701_, 3, v___x_815_);
lean_ctor_set(v___x_701_, 2, v_v_695_);
lean_ctor_set(v___x_701_, 1, v_k_694_);
lean_ctor_set(v___x_701_, 0, v___x_813_);
v___x_817_ = v___x_701_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_k_694_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v_v_695_);
lean_ctor_set(v_reuseFailAlloc_818_, 3, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_818_, 4, v_r_697_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
else
{
lean_object* v_k_820_; lean_object* v_v_821_; lean_object* v___x_823_; 
v_k_820_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_k_820_);
v_v_821_ = lean_ctor_get(v___x_703_, 1);
lean_inc(v_v_821_);
lean_dec_ref(v___x_703_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 3, v_r_697_);
v___x_823_ = v___x_777_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_size_693_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_k_694_);
lean_ctor_set(v_reuseFailAlloc_828_, 2, v_v_695_);
lean_ctor_set(v_reuseFailAlloc_828_, 3, v_r_697_);
lean_ctor_set(v_reuseFailAlloc_828_, 4, v_r_697_);
v___x_823_ = v_reuseFailAlloc_828_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_824_ = lean_unsigned_to_nat(2u);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 4, v___x_823_);
lean_ctor_set(v___x_701_, 3, v_r_697_);
lean_ctor_set(v___x_701_, 2, v_v_821_);
lean_ctor_set(v___x_701_, 1, v_k_820_);
lean_ctor_set(v___x_701_, 0, v___x_824_);
v___x_826_ = v___x_701_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_k_820_);
lean_ctor_set(v_reuseFailAlloc_827_, 2, v_v_821_);
lean_ctor_set(v_reuseFailAlloc_827_, 3, v_r_697_);
lean_ctor_set(v_reuseFailAlloc_827_, 4, v___x_823_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
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
lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_993_; 
lean_inc(v_r_697_);
lean_inc(v_v_695_);
lean_inc(v_k_694_);
v_isSharedCheck_993_ = !lean_is_exclusive(v_r_679_);
if (v_isSharedCheck_993_ == 0)
{
lean_object* v_unused_994_; lean_object* v_unused_995_; lean_object* v_unused_996_; lean_object* v_unused_997_; lean_object* v_unused_998_; 
v_unused_994_ = lean_ctor_get(v_r_679_, 4);
lean_dec(v_unused_994_);
v_unused_995_ = lean_ctor_get(v_r_679_, 3);
lean_dec(v_unused_995_);
v_unused_996_ = lean_ctor_get(v_r_679_, 2);
lean_dec(v_unused_996_);
v_unused_997_ = lean_ctor_get(v_r_679_, 1);
lean_dec(v_unused_997_);
v_unused_998_ = lean_ctor_get(v_r_679_, 0);
lean_dec(v_unused_998_);
v___x_842_ = v_r_679_;
v_isShared_843_ = v_isSharedCheck_993_;
goto v_resetjp_841_;
}
else
{
lean_dec(v_r_679_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_993_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v_tree_845_; 
v___x_844_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_694_, v_v_695_, v_l_696_, v_r_697_);
v_tree_845_ = lean_ctor_get(v___x_844_, 2);
lean_inc(v_tree_845_);
if (lean_obj_tag(v_tree_845_) == 0)
{
lean_object* v_k_846_; lean_object* v_v_847_; lean_object* v_size_848_; lean_object* v___x_849_; lean_object* v___x_850_; uint8_t v___x_851_; 
v_k_846_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_k_846_);
v_v_847_ = lean_ctor_get(v___x_844_, 1);
lean_inc(v_v_847_);
lean_dec_ref(v___x_844_);
v_size_848_ = lean_ctor_get(v_tree_845_, 0);
v___x_849_ = lean_unsigned_to_nat(3u);
v___x_850_ = lean_nat_mul(v___x_849_, v_size_848_);
v___x_851_ = lean_nat_dec_lt(v___x_850_, v_size_688_);
lean_dec(v___x_850_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
lean_dec(v_r_692_);
v___x_852_ = lean_nat_add(v___x_698_, v_size_688_);
v___x_853_ = lean_nat_add(v___x_852_, v_size_848_);
lean_dec(v___x_852_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 4, v_tree_845_);
lean_ctor_set(v___x_842_, 3, v_l_678_);
lean_ctor_set(v___x_842_, 2, v_v_847_);
lean_ctor_set(v___x_842_, 1, v_k_846_);
lean_ctor_set(v___x_842_, 0, v___x_853_);
v___x_855_ = v___x_842_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v_k_846_);
lean_ctor_set(v_reuseFailAlloc_856_, 2, v_v_847_);
lean_ctor_set(v_reuseFailAlloc_856_, 3, v_l_678_);
lean_ctor_set(v_reuseFailAlloc_856_, 4, v_tree_845_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
else
{
lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_922_; 
lean_inc(v_l_691_);
lean_inc(v_v_690_);
lean_inc(v_k_689_);
lean_inc(v_size_688_);
v_isSharedCheck_922_ = !lean_is_exclusive(v_l_678_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; lean_object* v_unused_924_; lean_object* v_unused_925_; lean_object* v_unused_926_; lean_object* v_unused_927_; 
v_unused_923_ = lean_ctor_get(v_l_678_, 4);
lean_dec(v_unused_923_);
v_unused_924_ = lean_ctor_get(v_l_678_, 3);
lean_dec(v_unused_924_);
v_unused_925_ = lean_ctor_get(v_l_678_, 2);
lean_dec(v_unused_925_);
v_unused_926_ = lean_ctor_get(v_l_678_, 1);
lean_dec(v_unused_926_);
v_unused_927_ = lean_ctor_get(v_l_678_, 0);
lean_dec(v_unused_927_);
v___x_858_ = v_l_678_;
v_isShared_859_ = v_isSharedCheck_922_;
goto v_resetjp_857_;
}
else
{
lean_dec(v_l_678_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_922_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v_size_860_; lean_object* v_size_861_; lean_object* v_k_862_; lean_object* v_v_863_; lean_object* v_l_864_; lean_object* v_r_865_; lean_object* v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v_size_860_ = lean_ctor_get(v_l_691_, 0);
v_size_861_ = lean_ctor_get(v_r_692_, 0);
v_k_862_ = lean_ctor_get(v_r_692_, 1);
v_v_863_ = lean_ctor_get(v_r_692_, 2);
v_l_864_ = lean_ctor_get(v_r_692_, 3);
v_r_865_ = lean_ctor_get(v_r_692_, 4);
v___x_866_ = lean_unsigned_to_nat(2u);
v___x_867_ = lean_nat_mul(v___x_866_, v_size_860_);
v___x_868_ = lean_nat_dec_lt(v_size_861_, v___x_867_);
lean_dec(v___x_867_);
if (v___x_868_ == 0)
{
lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_906_; 
lean_inc(v_r_865_);
lean_inc(v_l_864_);
lean_inc(v_v_863_);
lean_inc(v_k_862_);
lean_del_object(v___x_858_);
v_isSharedCheck_906_ = !lean_is_exclusive(v_r_692_);
if (v_isSharedCheck_906_ == 0)
{
lean_object* v_unused_907_; lean_object* v_unused_908_; lean_object* v_unused_909_; lean_object* v_unused_910_; lean_object* v_unused_911_; 
v_unused_907_ = lean_ctor_get(v_r_692_, 4);
lean_dec(v_unused_907_);
v_unused_908_ = lean_ctor_get(v_r_692_, 3);
lean_dec(v_unused_908_);
v_unused_909_ = lean_ctor_get(v_r_692_, 2);
lean_dec(v_unused_909_);
v_unused_910_ = lean_ctor_get(v_r_692_, 1);
lean_dec(v_unused_910_);
v_unused_911_ = lean_ctor_get(v_r_692_, 0);
lean_dec(v_unused_911_);
v___x_870_ = v_r_692_;
v_isShared_871_ = v_isSharedCheck_906_;
goto v_resetjp_869_;
}
else
{
lean_dec(v_r_692_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_906_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___x_894_; lean_object* v___y_896_; 
v___x_872_ = lean_nat_add(v___x_698_, v_size_688_);
lean_dec(v_size_688_);
v___x_873_ = lean_nat_add(v___x_872_, v_size_848_);
lean_dec(v___x_872_);
v___x_894_ = lean_nat_add(v___x_698_, v_size_860_);
if (lean_obj_tag(v_l_864_) == 0)
{
lean_object* v_size_904_; 
v_size_904_ = lean_ctor_get(v_l_864_, 0);
lean_inc(v_size_904_);
v___y_896_ = v_size_904_;
goto v___jp_895_;
}
else
{
lean_object* v___x_905_; 
v___x_905_ = lean_unsigned_to_nat(0u);
v___y_896_ = v___x_905_;
goto v___jp_895_;
}
v___jp_874_:
{
lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_878_ = lean_nat_add(v___y_875_, v___y_877_);
lean_dec(v___y_877_);
lean_dec(v___y_875_);
lean_inc_ref(v_tree_845_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 4, v_tree_845_);
lean_ctor_set(v___x_870_, 3, v_r_865_);
lean_ctor_set(v___x_870_, 2, v_v_847_);
lean_ctor_set(v___x_870_, 1, v_k_846_);
lean_ctor_set(v___x_870_, 0, v___x_878_);
v___x_880_ = v___x_870_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_k_846_);
lean_ctor_set(v_reuseFailAlloc_893_, 2, v_v_847_);
lean_ctor_set(v_reuseFailAlloc_893_, 3, v_r_865_);
lean_ctor_set(v_reuseFailAlloc_893_, 4, v_tree_845_);
v___x_880_ = v_reuseFailAlloc_893_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
v_isSharedCheck_887_ = !lean_is_exclusive(v_tree_845_);
if (v_isSharedCheck_887_ == 0)
{
lean_object* v_unused_888_; lean_object* v_unused_889_; lean_object* v_unused_890_; lean_object* v_unused_891_; lean_object* v_unused_892_; 
v_unused_888_ = lean_ctor_get(v_tree_845_, 4);
lean_dec(v_unused_888_);
v_unused_889_ = lean_ctor_get(v_tree_845_, 3);
lean_dec(v_unused_889_);
v_unused_890_ = lean_ctor_get(v_tree_845_, 2);
lean_dec(v_unused_890_);
v_unused_891_ = lean_ctor_get(v_tree_845_, 1);
lean_dec(v_unused_891_);
v_unused_892_ = lean_ctor_get(v_tree_845_, 0);
lean_dec(v_unused_892_);
v___x_882_ = v_tree_845_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_dec(v_tree_845_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 4, v___x_880_);
lean_ctor_set(v___x_882_, 3, v___y_876_);
lean_ctor_set(v___x_882_, 2, v_v_863_);
lean_ctor_set(v___x_882_, 1, v_k_862_);
lean_ctor_set(v___x_882_, 0, v___x_873_);
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_k_862_);
lean_ctor_set(v_reuseFailAlloc_886_, 2, v_v_863_);
lean_ctor_set(v_reuseFailAlloc_886_, 3, v___y_876_);
lean_ctor_set(v_reuseFailAlloc_886_, 4, v___x_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
v___jp_895_:
{
lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_897_ = lean_nat_add(v___x_894_, v___y_896_);
lean_dec(v___y_896_);
lean_dec(v___x_894_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 4, v_l_864_);
lean_ctor_set(v___x_842_, 3, v_l_691_);
lean_ctor_set(v___x_842_, 2, v_v_690_);
lean_ctor_set(v___x_842_, 1, v_k_689_);
lean_ctor_set(v___x_842_, 0, v___x_897_);
v___x_899_ = v___x_842_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_k_689_);
lean_ctor_set(v_reuseFailAlloc_903_, 2, v_v_690_);
lean_ctor_set(v_reuseFailAlloc_903_, 3, v_l_691_);
lean_ctor_set(v_reuseFailAlloc_903_, 4, v_l_864_);
v___x_899_ = v_reuseFailAlloc_903_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_900_; 
v___x_900_ = lean_nat_add(v___x_698_, v_size_848_);
if (lean_obj_tag(v_r_865_) == 0)
{
lean_object* v_size_901_; 
v_size_901_ = lean_ctor_get(v_r_865_, 0);
lean_inc(v_size_901_);
v___y_875_ = v___x_900_;
v___y_876_ = v___x_899_;
v___y_877_ = v_size_901_;
goto v___jp_874_;
}
else
{
lean_object* v___x_902_; 
v___x_902_ = lean_unsigned_to_nat(0u);
v___y_875_ = v___x_900_;
v___y_876_ = v___x_899_;
v___y_877_ = v___x_902_;
goto v___jp_874_;
}
}
}
}
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_912_ = lean_nat_add(v___x_698_, v_size_688_);
lean_dec(v_size_688_);
v___x_913_ = lean_nat_add(v___x_912_, v_size_848_);
lean_dec(v___x_912_);
v___x_914_ = lean_nat_add(v___x_698_, v_size_848_);
v___x_915_ = lean_nat_add(v___x_914_, v_size_861_);
lean_dec(v___x_914_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 4, v_tree_845_);
lean_ctor_set(v___x_842_, 3, v_r_692_);
lean_ctor_set(v___x_842_, 2, v_v_847_);
lean_ctor_set(v___x_842_, 1, v_k_846_);
lean_ctor_set(v___x_842_, 0, v___x_915_);
v___x_917_ = v___x_842_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_k_846_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_v_847_);
lean_ctor_set(v_reuseFailAlloc_921_, 3, v_r_692_);
lean_ctor_set(v_reuseFailAlloc_921_, 4, v_tree_845_);
v___x_917_ = v_reuseFailAlloc_921_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_919_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 4, v___x_917_);
lean_ctor_set(v___x_858_, 0, v___x_913_);
v___x_919_ = v___x_858_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_913_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_k_689_);
lean_ctor_set(v_reuseFailAlloc_920_, 2, v_v_690_);
lean_ctor_set(v_reuseFailAlloc_920_, 3, v_l_691_);
lean_ctor_set(v_reuseFailAlloc_920_, 4, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_691_) == 0)
{
lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_951_; 
lean_inc_ref(v_l_691_);
lean_inc(v_v_690_);
lean_inc(v_k_689_);
lean_inc(v_size_688_);
v_isSharedCheck_951_ = !lean_is_exclusive(v_l_678_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; lean_object* v_unused_953_; lean_object* v_unused_954_; lean_object* v_unused_955_; lean_object* v_unused_956_; 
v_unused_952_ = lean_ctor_get(v_l_678_, 4);
lean_dec(v_unused_952_);
v_unused_953_ = lean_ctor_get(v_l_678_, 3);
lean_dec(v_unused_953_);
v_unused_954_ = lean_ctor_get(v_l_678_, 2);
lean_dec(v_unused_954_);
v_unused_955_ = lean_ctor_get(v_l_678_, 1);
lean_dec(v_unused_955_);
v_unused_956_ = lean_ctor_get(v_l_678_, 0);
lean_dec(v_unused_956_);
v___x_929_ = v_l_678_;
v_isShared_930_ = v_isSharedCheck_951_;
goto v_resetjp_928_;
}
else
{
lean_dec(v_l_678_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_951_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
if (lean_obj_tag(v_r_692_) == 0)
{
lean_object* v_k_931_; lean_object* v_v_932_; lean_object* v_size_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_937_; 
v_k_931_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_k_931_);
v_v_932_ = lean_ctor_get(v___x_844_, 1);
lean_inc(v_v_932_);
lean_dec_ref(v___x_844_);
v_size_933_ = lean_ctor_get(v_r_692_, 0);
v___x_934_ = lean_nat_add(v___x_698_, v_size_688_);
lean_dec(v_size_688_);
v___x_935_ = lean_nat_add(v___x_698_, v_size_933_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 4, v_tree_845_);
lean_ctor_set(v___x_842_, 3, v_r_692_);
lean_ctor_set(v___x_842_, 2, v_v_932_);
lean_ctor_set(v___x_842_, 1, v_k_931_);
lean_ctor_set(v___x_842_, 0, v___x_935_);
v___x_937_ = v___x_842_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_k_931_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_v_932_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v_r_692_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v_tree_845_);
v___x_937_ = v_reuseFailAlloc_941_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_939_; 
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 4, v___x_937_);
lean_ctor_set(v___x_929_, 0, v___x_934_);
v___x_939_ = v___x_929_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_k_689_);
lean_ctor_set(v_reuseFailAlloc_940_, 2, v_v_690_);
lean_ctor_set(v_reuseFailAlloc_940_, 3, v_l_691_);
lean_ctor_set(v_reuseFailAlloc_940_, 4, v___x_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
else
{
lean_object* v_k_942_; lean_object* v_v_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
lean_dec(v_size_688_);
v_k_942_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_k_942_);
v_v_943_ = lean_ctor_get(v___x_844_, 1);
lean_inc(v_v_943_);
lean_dec_ref(v___x_844_);
v___x_944_ = lean_unsigned_to_nat(3u);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 4, v_r_692_);
lean_ctor_set(v___x_842_, 3, v_r_692_);
lean_ctor_set(v___x_842_, 2, v_v_943_);
lean_ctor_set(v___x_842_, 1, v_k_942_);
lean_ctor_set(v___x_842_, 0, v___x_698_);
v___x_946_ = v___x_842_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_k_942_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_v_943_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_r_692_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_r_692_);
v___x_946_ = v_reuseFailAlloc_950_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; 
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 4, v___x_946_);
lean_ctor_set(v___x_929_, 0, v___x_944_);
v___x_948_ = v___x_929_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_k_689_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_v_690_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v_l_691_);
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
}
}
else
{
if (lean_obj_tag(v_r_692_) == 0)
{
lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_981_; 
lean_inc(v_l_691_);
lean_inc(v_v_690_);
lean_inc(v_k_689_);
v_isSharedCheck_981_ = !lean_is_exclusive(v_l_678_);
if (v_isSharedCheck_981_ == 0)
{
lean_object* v_unused_982_; lean_object* v_unused_983_; lean_object* v_unused_984_; lean_object* v_unused_985_; lean_object* v_unused_986_; 
v_unused_982_ = lean_ctor_get(v_l_678_, 4);
lean_dec(v_unused_982_);
v_unused_983_ = lean_ctor_get(v_l_678_, 3);
lean_dec(v_unused_983_);
v_unused_984_ = lean_ctor_get(v_l_678_, 2);
lean_dec(v_unused_984_);
v_unused_985_ = lean_ctor_get(v_l_678_, 1);
lean_dec(v_unused_985_);
v_unused_986_ = lean_ctor_get(v_l_678_, 0);
lean_dec(v_unused_986_);
v___x_958_ = v_l_678_;
v_isShared_959_ = v_isSharedCheck_981_;
goto v_resetjp_957_;
}
else
{
lean_dec(v_l_678_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_981_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v_k_960_; lean_object* v_v_961_; lean_object* v_k_962_; lean_object* v_v_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_977_; 
v_k_960_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_k_960_);
v_v_961_ = lean_ctor_get(v___x_844_, 1);
lean_inc(v_v_961_);
lean_dec_ref(v___x_844_);
v_k_962_ = lean_ctor_get(v_r_692_, 1);
v_v_963_ = lean_ctor_get(v_r_692_, 2);
v_isSharedCheck_977_ = !lean_is_exclusive(v_r_692_);
if (v_isSharedCheck_977_ == 0)
{
lean_object* v_unused_978_; lean_object* v_unused_979_; lean_object* v_unused_980_; 
v_unused_978_ = lean_ctor_get(v_r_692_, 4);
lean_dec(v_unused_978_);
v_unused_979_ = lean_ctor_get(v_r_692_, 3);
lean_dec(v_unused_979_);
v_unused_980_ = lean_ctor_get(v_r_692_, 0);
lean_dec(v_unused_980_);
v___x_965_ = v_r_692_;
v_isShared_966_ = v_isSharedCheck_977_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_v_963_);
lean_inc(v_k_962_);
lean_dec(v_r_692_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_977_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_967_ = lean_unsigned_to_nat(3u);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 4, v_l_691_);
lean_ctor_set(v___x_965_, 3, v_l_691_);
lean_ctor_set(v___x_965_, 2, v_v_690_);
lean_ctor_set(v___x_965_, 1, v_k_689_);
lean_ctor_set(v___x_965_, 0, v___x_698_);
v___x_969_ = v___x_965_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_k_689_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v_v_690_);
lean_ctor_set(v_reuseFailAlloc_976_, 3, v_l_691_);
lean_ctor_set(v_reuseFailAlloc_976_, 4, v_l_691_);
v___x_969_ = v_reuseFailAlloc_976_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_971_; 
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 4, v_l_691_);
lean_ctor_set(v___x_842_, 3, v_l_691_);
lean_ctor_set(v___x_842_, 2, v_v_961_);
lean_ctor_set(v___x_842_, 1, v_k_960_);
lean_ctor_set(v___x_842_, 0, v___x_698_);
v___x_971_ = v___x_842_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_k_960_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v_v_961_);
lean_ctor_set(v_reuseFailAlloc_975_, 3, v_l_691_);
lean_ctor_set(v_reuseFailAlloc_975_, 4, v_l_691_);
v___x_971_ = v_reuseFailAlloc_975_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_973_; 
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 4, v___x_971_);
lean_ctor_set(v___x_958_, 3, v___x_969_);
lean_ctor_set(v___x_958_, 2, v_v_963_);
lean_ctor_set(v___x_958_, 1, v_k_962_);
lean_ctor_set(v___x_958_, 0, v___x_967_);
v___x_973_ = v___x_958_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_k_962_);
lean_ctor_set(v_reuseFailAlloc_974_, 2, v_v_963_);
lean_ctor_set(v_reuseFailAlloc_974_, 3, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_974_, 4, v___x_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
}
}
else
{
lean_object* v_k_987_; lean_object* v_v_988_; lean_object* v___x_989_; lean_object* v___x_991_; 
v_k_987_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_k_987_);
v_v_988_ = lean_ctor_get(v___x_844_, 1);
lean_inc(v_v_988_);
lean_dec_ref(v___x_844_);
v___x_989_ = lean_unsigned_to_nat(2u);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 4, v_r_692_);
lean_ctor_set(v___x_842_, 3, v_l_678_);
lean_ctor_set(v___x_842_, 2, v_v_988_);
lean_ctor_set(v___x_842_, 1, v_k_987_);
lean_ctor_set(v___x_842_, 0, v___x_989_);
v___x_991_ = v___x_842_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_k_987_);
lean_ctor_set(v_reuseFailAlloc_992_, 2, v_v_988_);
lean_ctor_set(v_reuseFailAlloc_992_, 3, v_l_678_);
lean_ctor_set(v_reuseFailAlloc_992_, 4, v_r_692_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
}
}
}
else
{
return v_l_678_;
}
}
else
{
return v_r_679_;
}
}
else
{
lean_object* v_val_999_; lean_object* v___x_1001_; 
v_val_999_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_val_999_);
lean_dec_ref_known(v___x_687_, 1);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 2, v_val_999_);
lean_ctor_set(v___x_681_, 1, v_k_673_);
v___x_1001_ = v___x_681_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_size_675_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_k_673_);
lean_ctor_set(v_reuseFailAlloc_1002_, 2, v_val_999_);
lean_ctor_set(v_reuseFailAlloc_1002_, 3, v_l_678_);
lean_ctor_set(v_reuseFailAlloc_1002_, 4, v_r_679_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
default: 
{
lean_object* v_impl_1003_; lean_object* v___x_1004_; 
lean_del_object(v___x_681_);
lean_dec(v_size_675_);
v_impl_1003_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_672_, v_k_673_, v_r_679_);
v___x_1004_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_676_, v_v_677_, v_l_678_, v_impl_1003_);
return v___x_1004_;
}
}
}
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = lean_box(0);
v___x_1007_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_672_, v___x_1006_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_dec(v_k_673_);
return v_t_674_;
}
else
{
lean_object* v_val_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_val_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_val_1008_);
lean_dec_ref_known(v___x_1007_, 1);
v___x_1009_ = lean_unsigned_to_nat(1u);
v___x_1010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
lean_ctor_set(v___x_1010_, 1, v_k_673_);
lean_ctor_set(v___x_1010_, 2, v_val_1008_);
lean_ctor_set(v___x_1010_, 3, v_t_674_);
lean_ctor_set(v___x_1010_, 4, v_t_674_);
return v___x_1010_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1011_, lean_object* v_i_1012_, lean_object* v_k_1013_){
_start:
{
lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_1014_ = lean_array_get_size(v_keys_1011_);
v___x_1015_ = lean_nat_dec_lt(v_i_1012_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_dec(v_i_1012_);
return v___x_1015_;
}
else
{
lean_object* v_k_x27_1016_; uint8_t v___x_1017_; 
v_k_x27_1016_ = lean_array_fget_borrowed(v_keys_1011_, v_i_1012_);
v___x_1017_ = lean_name_eq(v_k_1013_, v_k_x27_1016_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_unsigned_to_nat(1u);
v___x_1019_ = lean_nat_add(v_i_1012_, v___x_1018_);
lean_dec(v_i_1012_);
v_i_1012_ = v___x_1019_;
goto _start;
}
else
{
lean_dec(v_i_1012_);
return v___x_1017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1021_, lean_object* v_i_1022_, lean_object* v_k_1023_){
_start:
{
uint8_t v_res_1024_; lean_object* v_r_1025_; 
v_res_1024_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_1021_, v_i_1022_, v_k_1023_);
lean_dec(v_k_1023_);
lean_dec_ref(v_keys_1021_);
v_r_1025_ = lean_box(v_res_1024_);
return v_r_1025_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(lean_object* v_x_1026_, size_t v_x_1027_, lean_object* v_x_1028_){
_start:
{
if (lean_obj_tag(v_x_1026_) == 0)
{
lean_object* v_es_1029_; lean_object* v___x_1030_; size_t v___x_1031_; size_t v___x_1032_; lean_object* v_j_1033_; lean_object* v___x_1034_; 
v_es_1029_ = lean_ctor_get(v_x_1026_, 0);
v___x_1030_ = lean_box(2);
v___x_1031_ = ((size_t)31ULL);
v___x_1032_ = lean_usize_land(v_x_1027_, v___x_1031_);
v_j_1033_ = lean_usize_to_nat(v___x_1032_);
v___x_1034_ = lean_array_get_borrowed(v___x_1030_, v_es_1029_, v_j_1033_);
lean_dec(v_j_1033_);
switch(lean_obj_tag(v___x_1034_))
{
case 0:
{
lean_object* v_key_1035_; uint8_t v___x_1036_; 
v_key_1035_ = lean_ctor_get(v___x_1034_, 0);
v___x_1036_ = lean_name_eq(v_x_1028_, v_key_1035_);
return v___x_1036_;
}
case 1:
{
lean_object* v_node_1037_; size_t v___x_1038_; size_t v___x_1039_; 
v_node_1037_ = lean_ctor_get(v___x_1034_, 0);
v___x_1038_ = ((size_t)5ULL);
v___x_1039_ = lean_usize_shift_right(v_x_1027_, v___x_1038_);
v_x_1026_ = v_node_1037_;
v_x_1027_ = v___x_1039_;
goto _start;
}
default: 
{
uint8_t v___x_1041_; 
v___x_1041_ = 0;
return v___x_1041_;
}
}
}
else
{
lean_object* v_ks_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v_ks_1042_ = lean_ctor_get(v_x_1026_, 0);
v___x_1043_ = lean_unsigned_to_nat(0u);
v___x_1044_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_ks_1042_, v___x_1043_, v_x_1028_);
return v___x_1044_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___boxed(lean_object* v_x_1045_, lean_object* v_x_1046_, lean_object* v_x_1047_){
_start:
{
size_t v_x_4158__boxed_1048_; uint8_t v_res_1049_; lean_object* v_r_1050_; 
v_x_4158__boxed_1048_ = lean_unbox_usize(v_x_1046_);
lean_dec(v_x_1046_);
v_res_1049_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1045_, v_x_4158__boxed_1048_, v_x_1047_);
lean_dec(v_x_1047_);
lean_dec_ref(v_x_1045_);
v_r_1050_ = lean_box(v_res_1049_);
return v_r_1050_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1051_; uint64_t v___x_1052_; 
v___x_1051_ = lean_unsigned_to_nat(1723u);
v___x_1052_ = lean_uint64_of_nat(v___x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(lean_object* v_x_1053_, lean_object* v_x_1054_){
_start:
{
uint64_t v___y_1056_; 
if (lean_obj_tag(v_x_1054_) == 0)
{
uint64_t v___x_1059_; 
v___x_1059_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1056_ = v___x_1059_;
goto v___jp_1055_;
}
else
{
uint64_t v_hash_1060_; 
v_hash_1060_ = lean_ctor_get_uint64(v_x_1054_, sizeof(void*)*2);
v___y_1056_ = v_hash_1060_;
goto v___jp_1055_;
}
v___jp_1055_:
{
size_t v___x_1057_; uint8_t v___x_1058_; 
v___x_1057_ = lean_uint64_to_usize(v___y_1056_);
v___x_1058_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1053_, v___x_1057_, v_x_1054_);
return v___x_1058_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(lean_object* v_x_1061_, lean_object* v_x_1062_){
_start:
{
uint8_t v_res_1063_; lean_object* v_r_1064_; 
v_res_1063_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_1061_, v_x_1062_);
lean_dec(v_x_1062_);
lean_dec_ref(v_x_1061_);
v_r_1064_ = lean_box(v_res_1063_);
return v_r_1064_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(lean_object* v_tactics_1065_, lean_object* v_a_1066_, uint8_t v___x_1067_, lean_object* v_x_1068_, lean_object* v_____s_1069_){
_start:
{
lean_object* v_fst_1070_; lean_object* v_kinds_1071_; uint8_t v___x_1072_; 
v_fst_1070_ = lean_ctor_get(v_x_1068_, 0);
lean_inc(v_fst_1070_);
lean_dec_ref(v_x_1068_);
v_kinds_1071_ = lean_ctor_get(v_tactics_1065_, 1);
v___x_1072_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_kinds_1071_, v_fst_1070_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; 
lean_dec(v_fst_1070_);
lean_dec(v_a_1066_);
v___x_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1073_, 0, v_____s_1069_);
return v___x_1073_;
}
else
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1074_ = l_Lean_Name_toString(v_a_1066_, v___x_1067_);
v___x_1075_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1074_, v_fst_1070_, v_____s_1069_);
v___x_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
return v___x_1076_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(lean_object* v_tactics_1077_, lean_object* v_a_1078_, lean_object* v___x_1079_, lean_object* v_x_1080_, lean_object* v_____s_1081_){
_start:
{
uint8_t v___x_4220__boxed_1082_; lean_object* v_res_1083_; 
v___x_4220__boxed_1082_ = lean_unbox(v___x_1079_);
v_res_1083_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(v_tactics_1077_, v_a_1078_, v___x_4220__boxed_1082_, v_x_1080_, v_____s_1081_);
lean_dec_ref(v_tactics_1077_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_f_1084_, lean_object* v_keys_1085_, lean_object* v_vals_1086_, lean_object* v_i_1087_, lean_object* v_acc_1088_){
_start:
{
lean_object* v___x_1089_; uint8_t v___x_1090_; 
v___x_1089_ = lean_array_get_size(v_keys_1085_);
v___x_1090_ = lean_nat_dec_lt(v_i_1087_, v___x_1089_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; 
lean_dec(v_i_1087_);
lean_dec_ref(v_f_1084_);
v___x_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1091_, 0, v_acc_1088_);
return v___x_1091_;
}
else
{
lean_object* v_k_1092_; lean_object* v_v_1093_; lean_object* v___x_1094_; 
v_k_1092_ = lean_array_fget_borrowed(v_keys_1085_, v_i_1087_);
v_v_1093_ = lean_array_fget_borrowed(v_vals_1086_, v_i_1087_);
lean_inc_ref(v_f_1084_);
lean_inc(v_v_1093_);
lean_inc(v_k_1092_);
v___x_1094_ = lean_apply_3(v_f_1084_, v_acc_1088_, v_k_1092_, v_v_1093_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_dec(v_i_1087_);
lean_dec_ref(v_f_1084_);
return v___x_1094_;
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1095_);
lean_dec_ref_known(v___x_1094_, 1);
v___x_1096_ = lean_unsigned_to_nat(1u);
v___x_1097_ = lean_nat_add(v_i_1087_, v___x_1096_);
lean_dec(v_i_1087_);
v_i_1087_ = v___x_1097_;
v_acc_1088_ = v_a_1095_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_f_1099_, lean_object* v_keys_1100_, lean_object* v_vals_1101_, lean_object* v_i_1102_, lean_object* v_acc_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1099_, v_keys_1100_, v_vals_1101_, v_i_1102_, v_acc_1103_);
lean_dec_ref(v_vals_1101_);
lean_dec_ref(v_keys_1100_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object* v_f_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
if (lean_obj_tag(v_x_1106_) == 0)
{
lean_object* v_es_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1128_; 
v_es_1108_ = lean_ctor_get(v_x_1106_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_x_1106_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1110_ = v_x_1106_;
v_isShared_1111_ = v_isSharedCheck_1128_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_es_1108_);
lean_dec(v_x_1106_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1128_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v___x_1112_ = lean_unsigned_to_nat(0u);
v___x_1113_ = lean_array_get_size(v_es_1108_);
v___x_1114_ = lean_nat_dec_lt(v___x_1112_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1116_; 
lean_dec_ref(v_es_1108_);
lean_dec_ref(v_f_1105_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set_tag(v___x_1110_, 1);
lean_ctor_set(v___x_1110_, 0, v_x_1107_);
v___x_1116_ = v___x_1110_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_x_1107_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
else
{
uint8_t v___x_1118_; 
v___x_1118_ = lean_nat_dec_le(v___x_1113_, v___x_1113_);
if (v___x_1118_ == 0)
{
if (v___x_1114_ == 0)
{
lean_object* v___x_1120_; 
lean_dec_ref(v_es_1108_);
lean_dec_ref(v_f_1105_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set_tag(v___x_1110_, 1);
lean_ctor_set(v___x_1110_, 0, v_x_1107_);
v___x_1120_ = v___x_1110_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_x_1107_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
else
{
size_t v___x_1122_; size_t v___x_1123_; lean_object* v___x_1124_; 
lean_del_object(v___x_1110_);
v___x_1122_ = ((size_t)0ULL);
v___x_1123_ = lean_usize_of_nat(v___x_1113_);
v___x_1124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1105_, v_es_1108_, v___x_1122_, v___x_1123_, v_x_1107_);
lean_dec_ref(v_es_1108_);
return v___x_1124_;
}
}
else
{
size_t v___x_1125_; size_t v___x_1126_; lean_object* v___x_1127_; 
lean_del_object(v___x_1110_);
v___x_1125_ = ((size_t)0ULL);
v___x_1126_ = lean_usize_of_nat(v___x_1113_);
v___x_1127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1105_, v_es_1108_, v___x_1125_, v___x_1126_, v_x_1107_);
lean_dec_ref(v_es_1108_);
return v___x_1127_;
}
}
}
}
else
{
lean_object* v_ks_1129_; lean_object* v_vs_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v_ks_1129_ = lean_ctor_get(v_x_1106_, 0);
lean_inc_ref(v_ks_1129_);
v_vs_1130_ = lean_ctor_get(v_x_1106_, 1);
lean_inc_ref(v_vs_1130_);
lean_dec_ref_known(v_x_1106_, 2);
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1105_, v_ks_1129_, v_vs_1130_, v___x_1131_, v_x_1107_);
lean_dec_ref(v_vs_1130_);
lean_dec_ref(v_ks_1129_);
return v___x_1132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_f_1133_, lean_object* v_as_1134_, size_t v_i_1135_, size_t v_stop_1136_, lean_object* v_b_1137_){
_start:
{
lean_object* v_a_1139_; lean_object* v___y_1144_; uint8_t v___x_1146_; 
v___x_1146_ = lean_usize_dec_eq(v_i_1135_, v_stop_1136_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_array_uget_borrowed(v_as_1134_, v_i_1135_);
switch(lean_obj_tag(v___x_1147_))
{
case 0:
{
lean_object* v_key_1148_; lean_object* v_val_1149_; lean_object* v___x_1150_; 
v_key_1148_ = lean_ctor_get(v___x_1147_, 0);
v_val_1149_ = lean_ctor_get(v___x_1147_, 1);
lean_inc_ref(v_f_1133_);
lean_inc(v_val_1149_);
lean_inc(v_key_1148_);
v___x_1150_ = lean_apply_3(v_f_1133_, v_b_1137_, v_key_1148_, v_val_1149_);
v___y_1144_ = v___x_1150_;
goto v___jp_1143_;
}
case 1:
{
lean_object* v_node_1151_; lean_object* v___x_1152_; 
v_node_1151_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_node_1151_);
lean_inc_ref(v_f_1133_);
v___x_1152_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1133_, v_node_1151_, v_b_1137_);
v___y_1144_ = v___x_1152_;
goto v___jp_1143_;
}
default: 
{
v_a_1139_ = v_b_1137_;
goto v___jp_1138_;
}
}
}
else
{
lean_object* v___x_1153_; 
lean_dec_ref(v_f_1133_);
v___x_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1153_, 0, v_b_1137_);
return v___x_1153_;
}
v___jp_1138_:
{
size_t v___x_1140_; size_t v___x_1141_; 
v___x_1140_ = ((size_t)1ULL);
v___x_1141_ = lean_usize_add(v_i_1135_, v___x_1140_);
v_i_1135_ = v___x_1141_;
v_b_1137_ = v_a_1139_;
goto _start;
}
v___jp_1143_:
{
if (lean_obj_tag(v___y_1144_) == 0)
{
lean_dec_ref(v_f_1133_);
return v___y_1144_;
}
else
{
lean_object* v_a_1145_; 
v_a_1145_ = lean_ctor_get(v___y_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v___y_1144_, 1);
v_a_1139_ = v_a_1145_;
goto v___jp_1138_;
}
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
uint8_t v___x_4394__boxed_1218_; lean_object* v_res_1219_; 
v___x_4394__boxed_1218_ = lean_unbox(v___x_1215_);
v_res_1219_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1213_, v_a_1214_, v___x_4394__boxed_1218_, v_as_x27_1216_, v_b_1217_);
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
uint8_t v___x_4477__boxed_1285_; lean_object* v_res_1286_; 
v___x_4477__boxed_1285_ = lean_unbox(v___x_1280_);
v_res_1286_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(v_tactics_1278_, v_a_1279_, v___x_4477__boxed_1285_, v_as_1281_, v_as_x27_1282_, v_b_1283_, v_a_1284_);
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
size_t v_x_4486__boxed_1296_; uint8_t v_res_1297_; lean_object* v_r_1298_; 
v_x_4486__boxed_1296_ = lean_unbox_usize(v_x_1294_);
lean_dec(v_x_1294_);
v_res_1297_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(v_00_u03b2_1292_, v_x_1293_, v_x_4486__boxed_1296_, v_x_1295_);
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
v___x_1517_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
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
uint8_t v___x_16970__boxed_1593_; uint8_t v_res_1594_; lean_object* v_r_1595_; 
v___x_16970__boxed_1593_ = lean_unbox(v___x_1590_);
v_res_1594_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_16970__boxed_1593_, v_x1_1591_, v_x2_1592_);
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
lean_object* v___x_1704_; uint8_t v___x_1705_; 
v___x_1704_ = lean_unsigned_to_nat(0u);
v___x_1705_ = lean_nat_dec_eq(v_m_1699_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; uint8_t v___x_1707_; 
v___x_1706_ = lean_nat_sub(v_m_1699_, v___x_1698_);
lean_dec(v_m_1699_);
v___x_1707_ = lean_nat_dec_lt(v___x_1706_, v_x_1695_);
if (v___x_1707_ == 0)
{
v_x_1696_ = v___x_1706_;
goto _start;
}
else
{
lean_object* v___x_1709_; 
lean_dec(v___x_1706_);
lean_dec(v_x_1695_);
v___x_1709_ = lean_box(0);
return v___x_1709_;
}
}
else
{
lean_object* v___x_1710_; 
lean_dec(v_m_1699_);
lean_dec(v_x_1695_);
v___x_1710_ = lean_box(0);
return v___x_1710_;
}
}
}
else
{
lean_object* v___x_1711_; uint8_t v___x_1712_; 
lean_dec(v_x_1695_);
v___x_1711_ = lean_nat_add(v_m_1699_, v___x_1698_);
lean_dec(v_m_1699_);
v___x_1712_ = lean_nat_dec_le(v___x_1711_, v_x_1696_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; 
lean_dec(v___x_1711_);
lean_dec(v_x_1696_);
v___x_1713_ = lean_box(0);
return v___x_1713_;
}
else
{
v_x_1695_ = v___x_1711_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_as_1715_, lean_object* v_k_1716_, lean_object* v_x_1717_, lean_object* v_x_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_1715_, v_k_1716_, v_x_1717_, v_x_1718_);
lean_dec_ref(v_k_1716_);
lean_dec_ref(v_as_1715_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object* v_tac_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v___x_1724_; lean_object* v_env_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1724_ = lean_st_ref_get(v___y_1722_);
v_env_1728_ = lean_ctor_get(v___x_1724_, 0);
lean_inc_ref(v_env_1728_);
lean_dec(v___x_1724_);
v___x_1729_ = lean_box(1);
v___x_1730_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1728_, v_tac_1721_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v___x_1731_; lean_object* v_toEnvExtension_1732_; lean_object* v_asyncMode_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1731_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1732_ = lean_ctor_get(v___x_1731_, 0);
v_asyncMode_1733_ = lean_ctor_get(v_toEnvExtension_1732_, 2);
v___x_1734_ = lean_box(0);
v___x_1735_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1729_, v___x_1731_, v_env_1728_, v_asyncMode_1733_, v___x_1734_);
v___x_1736_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1735_, v_tac_1721_);
lean_dec(v_tac_1721_);
lean_dec(v___x_1735_);
v___x_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
return v___x_1737_;
}
else
{
lean_object* v_val_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1766_; 
v_val_1738_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1740_ = v___x_1730_;
v_isShared_1741_ = v_isSharedCheck_1766_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_val_1738_);
lean_dec(v___x_1730_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1766_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1742_; uint8_t v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; 
v___x_1742_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_1743_ = 0;
v___x_1744_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1729_, v___x_1742_, v_env_1728_, v_val_1738_, v___x_1743_);
lean_dec(v_val_1738_);
lean_dec_ref(v_env_1728_);
v___x_1745_ = lean_unsigned_to_nat(0u);
v___x_1746_ = lean_array_get_size(v___x_1744_);
v___x_1747_ = lean_nat_dec_lt(v___x_1745_, v___x_1746_);
if (v___x_1747_ == 0)
{
lean_dec_ref(v___x_1744_);
lean_del_object(v___x_1740_);
lean_dec(v_tac_1721_);
goto v___jp_1725_;
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
v___x_1748_ = lean_unsigned_to_nat(1u);
v___x_1749_ = lean_nat_sub(v___x_1746_, v___x_1748_);
v___x_1750_ = lean_nat_dec_le(v___x_1745_, v___x_1749_);
if (v___x_1750_ == 0)
{
lean_dec(v___x_1749_);
lean_dec_ref(v___x_1744_);
lean_del_object(v___x_1740_);
lean_dec(v_tac_1721_);
goto v___jp_1725_;
}
else
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1751_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
v___x_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1752_, 0, v_tac_1721_);
lean_ctor_set(v___x_1752_, 1, v___x_1751_);
v___x_1753_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v___x_1744_, v___x_1752_, v___x_1745_, v___x_1749_);
lean_dec_ref_known(v___x_1752_, 2);
lean_dec_ref(v___x_1744_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_del_object(v___x_1740_);
goto v___jp_1725_;
}
else
{
lean_object* v_val_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1765_; 
v_val_1754_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1756_ = v___x_1753_;
v_isShared_1757_ = v_isSharedCheck_1765_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_val_1754_);
lean_dec(v___x_1753_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1765_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v_snd_1758_; lean_object* v___x_1760_; 
v_snd_1758_ = lean_ctor_get(v_val_1754_, 1);
lean_inc(v_snd_1758_);
lean_dec(v_val_1754_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v_snd_1758_);
v___x_1760_ = v___x_1756_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_snd_1758_);
v___x_1760_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
lean_object* v___x_1762_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set_tag(v___x_1740_, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1760_);
v___x_1762_ = v___x_1740_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
}
}
}
}
v___jp_1725_:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = lean_box(0);
v___x_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
return v___x_1727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object* v_tac_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_1767_, v___y_1768_);
lean_dec(v___y_1768_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object* v_t_1771_, lean_object* v_k_1772_){
_start:
{
if (lean_obj_tag(v_t_1771_) == 0)
{
lean_object* v_k_1773_; lean_object* v_v_1774_; lean_object* v_l_1775_; lean_object* v_r_1776_; uint8_t v___x_1777_; 
v_k_1773_ = lean_ctor_get(v_t_1771_, 1);
v_v_1774_ = lean_ctor_get(v_t_1771_, 2);
v_l_1775_ = lean_ctor_get(v_t_1771_, 3);
v_r_1776_ = lean_ctor_get(v_t_1771_, 4);
v___x_1777_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1772_, v_k_1773_);
switch(v___x_1777_)
{
case 0:
{
v_t_1771_ = v_l_1775_;
goto _start;
}
case 1:
{
lean_object* v___x_1779_; 
lean_inc(v_v_1774_);
v___x_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1779_, 0, v_v_1774_);
return v___x_1779_;
}
default: 
{
v_t_1771_ = v_r_1776_;
goto _start;
}
}
}
else
{
lean_object* v___x_1781_; 
v___x_1781_ = lean_box(0);
return v___x_1781_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg___boxed(lean_object* v_t_1782_, lean_object* v_k_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_1782_, v_k_1783_);
lean_dec(v_k_1783_);
lean_dec(v_t_1782_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(lean_object* v_a_1785_, lean_object* v_x_1786_){
_start:
{
if (lean_obj_tag(v_x_1786_) == 0)
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_box(0);
return v___x_1787_;
}
else
{
lean_object* v_key_1788_; lean_object* v_value_1789_; lean_object* v_tail_1790_; uint8_t v___x_1791_; 
v_key_1788_ = lean_ctor_get(v_x_1786_, 0);
v_value_1789_ = lean_ctor_get(v_x_1786_, 1);
v_tail_1790_ = lean_ctor_get(v_x_1786_, 2);
v___x_1791_ = lean_name_eq(v_key_1788_, v_a_1785_);
if (v___x_1791_ == 0)
{
v_x_1786_ = v_tail_1790_;
goto _start;
}
else
{
lean_object* v___x_1793_; 
lean_inc(v_value_1789_);
v___x_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1793_, 0, v_value_1789_);
return v___x_1793_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg___boxed(lean_object* v_a_1794_, lean_object* v_x_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_1794_, v_x_1795_);
lean_dec(v_x_1795_);
lean_dec(v_a_1794_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(lean_object* v_m_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v_buckets_1799_; lean_object* v___x_1800_; uint64_t v___y_1802_; 
v_buckets_1799_ = lean_ctor_get(v_m_1797_, 1);
v___x_1800_ = lean_array_get_size(v_buckets_1799_);
if (lean_obj_tag(v_a_1798_) == 0)
{
uint64_t v___x_1816_; 
v___x_1816_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1802_ = v___x_1816_;
goto v___jp_1801_;
}
else
{
uint64_t v_hash_1817_; 
v_hash_1817_ = lean_ctor_get_uint64(v_a_1798_, sizeof(void*)*2);
v___y_1802_ = v_hash_1817_;
goto v___jp_1801_;
}
v___jp_1801_:
{
uint64_t v___x_1803_; uint64_t v___x_1804_; uint64_t v_fold_1805_; uint64_t v___x_1806_; uint64_t v___x_1807_; uint64_t v___x_1808_; size_t v___x_1809_; size_t v___x_1810_; size_t v___x_1811_; size_t v___x_1812_; size_t v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1803_ = 32ULL;
v___x_1804_ = lean_uint64_shift_right(v___y_1802_, v___x_1803_);
v_fold_1805_ = lean_uint64_xor(v___y_1802_, v___x_1804_);
v___x_1806_ = 16ULL;
v___x_1807_ = lean_uint64_shift_right(v_fold_1805_, v___x_1806_);
v___x_1808_ = lean_uint64_xor(v_fold_1805_, v___x_1807_);
v___x_1809_ = lean_uint64_to_usize(v___x_1808_);
v___x_1810_ = lean_usize_of_nat(v___x_1800_);
v___x_1811_ = ((size_t)1ULL);
v___x_1812_ = lean_usize_sub(v___x_1810_, v___x_1811_);
v___x_1813_ = lean_usize_land(v___x_1809_, v___x_1812_);
v___x_1814_ = lean_array_uget_borrowed(v_buckets_1799_, v___x_1813_);
v___x_1815_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_1798_, v___x_1814_);
return v___x_1815_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg___boxed(lean_object* v_m_1818_, lean_object* v_a_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_1818_, v_a_1819_);
lean_dec(v_a_1819_);
lean_dec_ref(v_m_1818_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_keys_1821_, lean_object* v_vals_1822_, lean_object* v_i_1823_, lean_object* v_k_1824_){
_start:
{
lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1825_ = lean_array_get_size(v_keys_1821_);
v___x_1826_ = lean_nat_dec_lt(v_i_1823_, v___x_1825_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; 
lean_dec(v_i_1823_);
v___x_1827_ = lean_box(0);
return v___x_1827_;
}
else
{
lean_object* v_k_x27_1828_; uint8_t v___x_1829_; 
v_k_x27_1828_ = lean_array_fget_borrowed(v_keys_1821_, v_i_1823_);
v___x_1829_ = lean_name_eq(v_k_1824_, v_k_x27_1828_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = lean_unsigned_to_nat(1u);
v___x_1831_ = lean_nat_add(v_i_1823_, v___x_1830_);
lean_dec(v_i_1823_);
v_i_1823_ = v___x_1831_;
goto _start;
}
else
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = lean_array_fget_borrowed(v_vals_1822_, v_i_1823_);
lean_dec(v_i_1823_);
lean_inc(v___x_1833_);
v___x_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
return v___x_1834_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object* v_keys_1835_, lean_object* v_vals_1836_, lean_object* v_i_1837_, lean_object* v_k_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_1835_, v_vals_1836_, v_i_1837_, v_k_1838_);
lean_dec(v_k_1838_);
lean_dec_ref(v_vals_1836_);
lean_dec_ref(v_keys_1835_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object* v_x_1840_, size_t v_x_1841_, lean_object* v_x_1842_){
_start:
{
if (lean_obj_tag(v_x_1840_) == 0)
{
lean_object* v_es_1843_; lean_object* v___x_1844_; size_t v___x_1845_; size_t v___x_1846_; lean_object* v_j_1847_; lean_object* v___x_1848_; 
v_es_1843_ = lean_ctor_get(v_x_1840_, 0);
v___x_1844_ = lean_box(2);
v___x_1845_ = ((size_t)31ULL);
v___x_1846_ = lean_usize_land(v_x_1841_, v___x_1845_);
v_j_1847_ = lean_usize_to_nat(v___x_1846_);
v___x_1848_ = lean_array_get_borrowed(v___x_1844_, v_es_1843_, v_j_1847_);
lean_dec(v_j_1847_);
switch(lean_obj_tag(v___x_1848_))
{
case 0:
{
lean_object* v_key_1849_; lean_object* v_val_1850_; uint8_t v___x_1851_; 
v_key_1849_ = lean_ctor_get(v___x_1848_, 0);
v_val_1850_ = lean_ctor_get(v___x_1848_, 1);
v___x_1851_ = lean_name_eq(v_x_1842_, v_key_1849_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; 
v___x_1852_ = lean_box(0);
return v___x_1852_;
}
else
{
lean_object* v___x_1853_; 
lean_inc(v_val_1850_);
v___x_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1853_, 0, v_val_1850_);
return v___x_1853_;
}
}
case 1:
{
lean_object* v_node_1854_; size_t v___x_1855_; size_t v___x_1856_; 
v_node_1854_ = lean_ctor_get(v___x_1848_, 0);
v___x_1855_ = ((size_t)5ULL);
v___x_1856_ = lean_usize_shift_right(v_x_1841_, v___x_1855_);
v_x_1840_ = v_node_1854_;
v_x_1841_ = v___x_1856_;
goto _start;
}
default: 
{
lean_object* v___x_1858_; 
v___x_1858_ = lean_box(0);
return v___x_1858_;
}
}
}
else
{
lean_object* v_ks_1859_; lean_object* v_vs_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v_ks_1859_ = lean_ctor_get(v_x_1840_, 0);
v_vs_1860_ = lean_ctor_get(v_x_1840_, 1);
v___x_1861_ = lean_unsigned_to_nat(0u);
v___x_1862_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_ks_1859_, v_vs_1860_, v___x_1861_, v_x_1842_);
return v___x_1862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_1863_, lean_object* v_x_1864_, lean_object* v_x_1865_){
_start:
{
size_t v_x_17346__boxed_1866_; lean_object* v_res_1867_; 
v_x_17346__boxed_1866_ = lean_unbox_usize(v_x_1864_);
lean_dec(v_x_1864_);
v_res_1867_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1863_, v_x_17346__boxed_1866_, v_x_1865_);
lean_dec(v_x_1865_);
lean_dec_ref(v_x_1863_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object* v_x_1868_, lean_object* v_x_1869_){
_start:
{
uint64_t v___y_1871_; 
if (lean_obj_tag(v_x_1869_) == 0)
{
uint64_t v___x_1874_; 
v___x_1874_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1871_ = v___x_1874_;
goto v___jp_1870_;
}
else
{
uint64_t v_hash_1875_; 
v_hash_1875_ = lean_ctor_get_uint64(v_x_1869_, sizeof(void*)*2);
v___y_1871_ = v_hash_1875_;
goto v___jp_1870_;
}
v___jp_1870_:
{
size_t v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = lean_uint64_to_usize(v___y_1871_);
v___x_1873_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1868_, v___x_1872_, v_x_1869_);
return v___x_1873_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object* v_x_1876_, lean_object* v_x_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_1876_, v_x_1877_);
lean_dec(v_x_1877_);
lean_dec_ref(v_x_1876_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object* v_x_1879_, lean_object* v_x_1880_){
_start:
{
uint8_t v_stage_u2081_1881_; 
v_stage_u2081_1881_ = lean_ctor_get_uint8(v_x_1879_, sizeof(void*)*2);
if (v_stage_u2081_1881_ == 0)
{
lean_object* v_map_u2081_1882_; lean_object* v_map_u2082_1883_; lean_object* v___x_1884_; 
v_map_u2081_1882_ = lean_ctor_get(v_x_1879_, 0);
v_map_u2082_1883_ = lean_ctor_get(v_x_1879_, 1);
v___x_1884_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_1882_, v_x_1880_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_map_u2082_1883_, v_x_1880_);
return v___x_1885_;
}
else
{
return v___x_1884_;
}
}
else
{
lean_object* v_map_u2081_1886_; lean_object* v___x_1887_; 
v_map_u2081_1886_ = lean_ctor_get(v_x_1879_, 0);
v___x_1887_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_1886_, v_x_1880_);
return v___x_1887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg___boxed(lean_object* v_x_1888_, lean_object* v_x_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_1888_, v_x_1889_);
lean_dec(v_x_1889_);
lean_dec_ref(v_x_1888_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object* v_firsts_1891_, lean_object* v_n_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1911_; lean_object* v_val_1912_; lean_object* v___x_1914_; lean_object* v___y_1916_; lean_object* v_env_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1914_ = lean_st_ref_get(v___y_1894_);
v_env_1931_ = lean_ctor_get(v___x_1914_, 0);
lean_inc_ref(v_env_1931_);
lean_dec(v___x_1914_);
v___x_1932_ = l_Lean_Environment_constants(v_env_1931_);
v___x_1933_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v___x_1932_, v_n_1892_);
lean_dec_ref(v___x_1932_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v___x_1934_; 
v___x_1934_ = lean_box(0);
v___y_1916_ = v___x_1934_;
goto v___jp_1915_;
}
else
{
lean_object* v_val_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v_val_1935_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_val_1935_);
lean_dec_ref_known(v___x_1933_, 1);
v___x_1936_ = l_Lean_ConstantInfo_levelParams(v_val_1935_);
lean_dec(v_val_1935_);
v___x_1937_ = lean_box(0);
v___x_1938_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(v___x_1936_, v___x_1937_);
v___y_1916_ = v___x_1938_;
goto v___jp_1915_;
}
v___jp_1896_:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1899_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_1900_ = l_Lean_Expr_const___override(v_n_1892_, v___y_1897_);
v___x_1901_ = lean_unsigned_to_nat(32u);
v___x_1902_ = lean_mk_empty_array_with_capacity(v___x_1901_);
lean_dec_ref(v___x_1902_);
v___x_1903_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2);
v___x_1904_ = lean_box(0);
v___x_1905_ = 0;
v___x_1906_ = l_Lean_MessageData_withExprHover(v___y_1898_, v___x_1900_, v___x_1903_, v___x_1904_, v___x_1904_, v___x_1904_, v___x_1905_);
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1899_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
lean_ctor_set(v___x_1908_, 1, v___x_1899_);
v___x_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
return v___x_1909_;
}
v___jp_1910_:
{
lean_object* v___x_1913_; 
v___x_1913_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1913_, 0, v_val_1912_);
v___y_1897_ = v___y_1911_;
v___y_1898_ = v___x_1913_;
goto v___jp_1896_;
}
v___jp_1915_:
{
lean_object* v___x_1917_; lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1930_; 
lean_inc(v_n_1892_);
v___x_1917_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_n_1892_, v___y_1894_);
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1920_ = v___x_1917_;
v_isShared_1921_ = v_isSharedCheck_1930_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1917_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1930_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
if (lean_obj_tag(v_a_1918_) == 0)
{
lean_object* v___x_1922_; 
v___x_1922_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_firsts_1891_, v_n_1892_);
if (lean_obj_tag(v___x_1922_) == 0)
{
uint8_t v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1923_ = 1;
lean_inc(v_n_1892_);
v___x_1924_ = l_Lean_Name_toString(v_n_1892_, v___x_1923_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set_tag(v___x_1920_, 3);
lean_ctor_set(v___x_1920_, 0, v___x_1924_);
v___x_1926_ = v___x_1920_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
v___y_1897_ = v___y_1916_;
v___y_1898_ = v___x_1926_;
goto v___jp_1896_;
}
}
else
{
lean_object* v_val_1928_; 
lean_del_object(v___x_1920_);
v_val_1928_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_val_1928_);
lean_dec_ref_known(v___x_1922_, 1);
v___y_1911_ = v___y_1916_;
v_val_1912_ = v_val_1928_;
goto v___jp_1910_;
}
}
else
{
lean_object* v_val_1929_; 
lean_del_object(v___x_1920_);
v_val_1929_ = lean_ctor_get(v_a_1918_, 0);
lean_inc(v_val_1929_);
lean_dec_ref_known(v_a_1918_, 1);
v___y_1911_ = v___y_1916_;
v_val_1912_ = v_val_1929_;
goto v___jp_1910_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object* v_firsts_1939_, lean_object* v_n_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_firsts_1939_, v_n_1940_, v___y_1941_, v___y_1942_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v_firsts_1939_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object* v_a_1945_, lean_object* v_x_1946_, lean_object* v_x_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
if (lean_obj_tag(v_x_1946_) == 0)
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = l_List_reverse___redArg(v_x_1947_);
v___x_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
return v___x_1952_;
}
else
{
lean_object* v_head_1953_; lean_object* v_tail_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1972_; 
v_head_1953_ = lean_ctor_get(v_x_1946_, 0);
v_tail_1954_ = lean_ctor_get(v_x_1946_, 1);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_x_1946_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1956_ = v_x_1946_;
v_isShared_1957_ = v_isSharedCheck_1972_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_tail_1954_);
lean_inc(v_head_1953_);
lean_dec(v_x_1946_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1972_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1958_; 
v___x_1958_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_a_1945_, v_head_1953_, v___y_1948_, v___y_1949_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1961_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1959_);
lean_dec_ref_known(v___x_1958_, 1);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 1, v_x_1947_);
lean_ctor_set(v___x_1956_, 0, v_a_1959_);
v___x_1961_ = v___x_1956_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1959_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_x_1947_);
v___x_1961_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
v_x_1946_ = v_tail_1954_;
v_x_1947_ = v___x_1961_;
goto _start;
}
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_del_object(v___x_1956_);
lean_dec(v_tail_1954_);
lean_dec(v_x_1947_);
v_a_1964_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1958_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1958_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object* v_a_1973_, lean_object* v_x_1974_, lean_object* v_x_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_1973_, v_x_1974_, v_x_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v_a_1973_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object* v_val_1980_, lean_object* v___x_1981_, lean_object* v___x_1982_, lean_object* v_a_1983_, lean_object* v_b_1984_){
_start:
{
lean_object* v_it_1986_; lean_object* v_startInclusive_1987_; lean_object* v_endExclusive_1988_; 
if (lean_obj_tag(v_a_1983_) == 0)
{
lean_object* v_currPos_1993_; lean_object* v_searcher_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2020_; 
v_currPos_1993_ = lean_ctor_get(v_a_1983_, 0);
v_searcher_1994_ = lean_ctor_get(v_a_1983_, 1);
v_isSharedCheck_2020_ = !lean_is_exclusive(v_a_1983_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_1996_ = v_a_1983_;
v_isShared_1997_ = v_isSharedCheck_2020_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_searcher_1994_);
lean_inc(v_currPos_1993_);
lean_dec(v_a_1983_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2020_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v_startInclusive_1998_; lean_object* v_endExclusive_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v_startInclusive_1998_ = lean_ctor_get(v___x_1981_, 1);
v_endExclusive_1999_ = lean_ctor_get(v___x_1981_, 2);
v___x_2000_ = lean_nat_sub(v_endExclusive_1999_, v_startInclusive_1998_);
v___x_2001_ = lean_nat_dec_eq(v_searcher_1994_, v___x_2000_);
lean_dec(v___x_2000_);
if (v___x_2001_ == 0)
{
uint32_t v___x_2002_; uint32_t v___x_2003_; uint8_t v___x_2004_; 
v___x_2002_ = 10;
v___x_2003_ = lean_string_utf8_get_fast(v_val_1980_, v_searcher_1994_);
v___x_2004_ = lean_uint32_dec_eq(v___x_2003_, v___x_2002_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2005_ = lean_string_utf8_next_fast(v_val_1980_, v_searcher_1994_);
lean_dec(v_searcher_1994_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 1, v___x_2005_);
v___x_2007_ = v___x_1996_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_currPos_1993_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
v_a_1983_ = v___x_2007_;
goto _start;
}
}
else
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v_slice_2013_; lean_object* v_nextIt_2015_; 
v___x_2010_ = lean_string_utf8_next_fast(v_val_1980_, v_searcher_1994_);
v___x_2011_ = lean_nat_sub(v___x_2010_, v_searcher_1994_);
v___x_2012_ = lean_nat_add(v_searcher_1994_, v___x_2011_);
lean_dec(v___x_2011_);
v_slice_2013_ = l_String_Slice_subslice_x21(v___x_1981_, v_currPos_1993_, v_searcher_1994_);
lean_inc(v___x_2012_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 1, v___x_2012_);
lean_ctor_set(v___x_1996_, 0, v___x_2012_);
v_nextIt_2015_ = v___x_1996_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2012_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v___x_2012_);
v_nextIt_2015_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
lean_object* v_startInclusive_2016_; lean_object* v_endExclusive_2017_; 
v_startInclusive_2016_ = lean_ctor_get(v_slice_2013_, 0);
lean_inc(v_startInclusive_2016_);
v_endExclusive_2017_ = lean_ctor_get(v_slice_2013_, 1);
lean_inc(v_endExclusive_2017_);
lean_dec_ref(v_slice_2013_);
v_it_1986_ = v_nextIt_2015_;
v_startInclusive_1987_ = v_startInclusive_2016_;
v_endExclusive_1988_ = v_endExclusive_2017_;
goto v___jp_1985_;
}
}
}
else
{
lean_object* v___x_2019_; 
lean_del_object(v___x_1996_);
lean_dec(v_searcher_1994_);
v___x_2019_ = lean_box(1);
lean_inc(v___x_1982_);
v_it_1986_ = v___x_2019_;
v_startInclusive_1987_ = v_currPos_1993_;
v_endExclusive_1988_ = v___x_1982_;
goto v___jp_1985_;
}
}
}
else
{
lean_dec(v___x_1982_);
return v_b_1984_;
}
v___jp_1985_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1989_ = lean_string_utf8_extract(v_val_1980_, v_startInclusive_1987_, v_endExclusive_1988_);
lean_dec(v_endExclusive_1988_);
lean_dec(v_startInclusive_1987_);
v___x_1990_ = l_Lean_stringToMessageData(v___x_1989_);
v___x_1991_ = lean_array_push(v_b_1984_, v___x_1990_);
v_a_1983_ = v_it_1986_;
v_b_1984_ = v___x_1991_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object* v_val_2021_, lean_object* v___x_2022_, lean_object* v___x_2023_, lean_object* v_a_2024_, lean_object* v_b_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2021_, v___x_2022_, v___x_2023_, v_a_2024_, v_b_2025_);
lean_dec_ref(v___x_2022_);
lean_dec_ref(v_val_2021_);
return v_res_2026_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1));
v___x_2031_ = l_Lean_stringToMessageData(v___x_2030_);
return v___x_2031_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4(void){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3));
v___x_2034_ = l_Lean_stringToMessageData(v___x_2033_);
return v___x_2034_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6(void){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5));
v___x_2037_ = l_Lean_stringToMessageData(v___x_2036_);
return v___x_2037_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9(void){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8));
v___x_2042_ = l_Lean_MessageData_ofFormat(v___x_2041_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_x_2045_, lean_object* v_x_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
if (lean_obj_tag(v_x_2045_) == 0)
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = l_List_reverse___redArg(v_x_2046_);
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
return v___x_2051_;
}
else
{
lean_object* v_head_2052_; lean_object* v_tail_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2151_; 
v_head_2052_ = lean_ctor_get(v_x_2045_, 0);
v_tail_2053_ = lean_ctor_get(v_x_2045_, 1);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_x_2045_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2055_ = v_x_2045_;
v_isShared_2056_ = v_isSharedCheck_2151_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_tail_2053_);
lean_inc(v_head_2052_);
lean_dec(v_x_2045_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2151_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v_snd_2070_; lean_object* v_fst_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2150_; 
v_snd_2070_ = lean_ctor_get(v_head_2052_, 1);
v_fst_2071_ = lean_ctor_get(v_head_2052_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_head_2052_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2073_ = v_head_2052_;
v_isShared_2074_ = v_isSharedCheck_2150_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_snd_2070_);
lean_inc(v_fst_2071_);
lean_dec(v_head_2052_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2150_;
goto v_resetjp_2072_;
}
v___jp_2057_:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2067_; 
v___x_2062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___y_2059_);
lean_ctor_set(v___x_2062_, 1, v___y_2061_);
v___x_2063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
lean_ctor_set(v___x_2063_, 1, v___y_2058_);
v___x_2064_ = l_Lean_MessageData_nestD(v___x_2063_);
lean_inc_ref(v___y_2060_);
v___x_2065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___y_2060_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 1, v_x_2046_);
lean_ctor_set(v___x_2055_, 0, v___x_2065_);
v___x_2067_ = v___x_2055_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v_x_2046_);
v___x_2067_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
v_x_2045_ = v_tail_2053_;
v_x_2046_ = v___x_2067_;
goto _start;
}
}
v_resetjp_2072_:
{
lean_object* v_fst_2075_; lean_object* v_snd_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2149_; 
v_fst_2075_ = lean_ctor_get(v_snd_2070_, 0);
v_snd_2076_ = lean_ctor_get(v_snd_2070_, 1);
v_isSharedCheck_2149_ = !lean_is_exclusive(v_snd_2070_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2078_ = v_snd_2070_;
v_isShared_2079_ = v_isSharedCheck_2149_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_snd_2076_);
lean_inc(v_fst_2075_);
lean_dec(v_snd_2070_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2149_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v_a_2103_; lean_object* v___y_2120_; lean_object* v___x_2129_; 
v___x_2129_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2044_, v_fst_2071_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v___x_2130_; 
v___x_2130_ = l_Lean_MessageData_nil;
v_a_2103_ = v___x_2130_;
goto v___jp_2102_;
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
v_a_2103_ = v___x_2148_;
goto v___jp_2102_;
}
}
v___jp_2080_:
{
lean_object* v___x_2086_; 
if (v_isShared_2079_ == 0)
{
lean_ctor_set_tag(v___x_2078_, 7);
lean_ctor_set(v___x_2078_, 1, v___y_2084_);
lean_ctor_set(v___x_2078_, 0, v___y_2082_);
v___x_2086_ = v___x_2078_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___y_2082_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v___y_2084_);
v___x_2086_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
if (lean_obj_tag(v_snd_2076_) == 0)
{
lean_object* v___x_2087_; 
lean_del_object(v___x_2073_);
v___x_2087_ = l_Lean_MessageData_nil;
v___y_2058_ = v___y_2081_;
v___y_2059_ = v___x_2086_;
v___y_2060_ = v___y_2083_;
v___y_2061_ = v___x_2087_;
goto v___jp_2057_;
}
else
{
lean_object* v_val_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2099_; 
v_val_2088_ = lean_ctor_get(v_snd_2076_, 0);
lean_inc_n(v_val_2088_, 2);
lean_dec_ref_known(v_snd_2076_, 1);
v___x_2089_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2090_ = lean_unsigned_to_nat(0u);
v___x_2091_ = lean_string_utf8_byte_size(v_val_2088_);
v___x_2092_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2092_, 0, v_val_2088_);
lean_ctor_set(v___x_2092_, 1, v___x_2090_);
lean_ctor_set(v___x_2092_, 2, v___x_2091_);
v___x_2093_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v___x_2092_);
v___x_2094_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0));
v___x_2095_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2088_, v___x_2092_, v___x_2091_, v___x_2093_, v___x_2094_);
lean_dec_ref_known(v___x_2092_, 3);
lean_dec(v_val_2088_);
v___x_2096_ = lean_array_to_list(v___x_2095_);
v___x_2097_ = l_Lean_MessageData_joinSep(v___x_2096_, v___x_2089_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set_tag(v___x_2073_, 7);
lean_ctor_set(v___x_2073_, 1, v___x_2097_);
lean_ctor_set(v___x_2073_, 0, v___x_2089_);
v___x_2099_ = v___x_2073_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v___x_2097_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
v___y_2058_ = v___y_2081_;
v___y_2059_ = v___x_2086_;
v___y_2060_ = v___y_2083_;
v___y_2061_ = v___x_2099_;
goto v___jp_2057_;
}
}
}
}
v___jp_2102_:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; uint8_t v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; uint8_t v___x_2112_; 
v___x_2104_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2);
v___x_2105_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
lean_inc(v_fst_2071_);
v___x_2106_ = l_Lean_MessageData_ofName(v_fst_2071_);
v___x_2107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2105_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
v___x_2108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
lean_ctor_set(v___x_2108_, 1, v___x_2105_);
v___x_2109_ = 1;
v___x_2110_ = l_Lean_Name_toString(v_fst_2071_, v___x_2109_);
v___x_2111_ = lean_string_dec_eq(v___x_2110_, v_fst_2075_);
lean_dec_ref(v___x_2110_);
v___x_2112_ = lean_bool_not(v___x_2111_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; 
lean_dec(v_fst_2075_);
v___x_2113_ = l_Lean_MessageData_nil;
v___y_2081_ = v_a_2103_;
v___y_2082_ = v___x_2108_;
v___y_2083_ = v___x_2104_;
v___y_2084_ = v___x_2113_;
goto v___jp_2080_;
}
else
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2114_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4);
v___x_2115_ = l_Lean_stringToMessageData(v_fst_2075_);
v___x_2116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2114_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
v___x_2117_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6);
v___x_2118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2116_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___y_2081_ = v_a_2103_;
v___y_2082_ = v___x_2108_;
v___y_2083_ = v___x_2104_;
v___y_2084_ = v___x_2118_;
goto v___jp_2080_;
}
}
v___jp_2119_:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2121_ = lean_array_to_list(v___y_2120_);
v___x_2122_ = lean_box(0);
v___x_2123_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_2043_, v___x_2121_, v___x_2122_, v___y_2047_, v___y_2048_);
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
v_a_2103_ = v___x_2128_;
goto v___jp_2102_;
}
else
{
lean_del_object(v___x_2078_);
lean_dec(v_snd_2076_);
lean_dec(v_fst_2075_);
lean_del_object(v___x_2073_);
lean_dec(v_fst_2071_);
lean_del_object(v___x_2055_);
lean_dec(v_tail_2053_);
lean_dec(v_x_2046_);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(uint8_t v___y_2161_, uint8_t v_suppressElabErrors_2162_, lean_object* v_x_2163_){
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
return v___y_2161_;
}
else
{
return v_suppressElabErrors_2162_;
}
}
else
{
return v___y_2161_;
}
}
else
{
return v___y_2161_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed(lean_object* v___y_2168_, lean_object* v_suppressElabErrors_2169_, lean_object* v_x_2170_){
_start:
{
uint8_t v___y_17968__boxed_2171_; uint8_t v_suppressElabErrors_boxed_2172_; uint8_t v_res_2173_; lean_object* v_r_2174_; 
v___y_17968__boxed_2171_ = lean_unbox(v___y_2168_);
v_suppressElabErrors_boxed_2172_ = lean_unbox(v_suppressElabErrors_2169_);
v_res_2173_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(v___y_17968__boxed_2171_, v_suppressElabErrors_boxed_2172_, v_x_2170_);
lean_dec(v_x_2170_);
v_r_2174_ = lean_box(v_res_2173_);
return v_r_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(lean_object* v_ref_2175_, lean_object* v_msgData_2176_, uint8_t v_severity_2177_, uint8_t v_isSilent_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v___y_2183_; lean_object* v___y_2184_; uint8_t v___y_2185_; lean_object* v___y_2186_; uint8_t v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; uint8_t v___y_2246_; lean_object* v___y_2247_; uint8_t v___y_2248_; uint8_t v___y_2249_; lean_object* v___y_2250_; uint8_t v___y_2274_; uint8_t v___y_2275_; lean_object* v___y_2276_; uint8_t v___y_2277_; lean_object* v___y_2278_; uint8_t v___y_2282_; uint8_t v___y_2283_; uint8_t v___y_2284_; uint8_t v___x_2299_; uint8_t v___y_2301_; uint8_t v___y_2302_; uint8_t v___y_2303_; uint8_t v___y_2305_; uint8_t v___x_2317_; 
v___x_2299_ = 2;
v___x_2317_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2177_, v___x_2299_);
if (v___x_2317_ == 0)
{
v___y_2305_ = v___x_2317_;
goto v___jp_2304_;
}
else
{
uint8_t v___x_2318_; 
lean_inc_ref(v_msgData_2176_);
v___x_2318_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2176_);
v___y_2305_ = v___x_2318_;
goto v___jp_2304_;
}
v___jp_2182_:
{
lean_object* v___x_2191_; 
v___x_2191_ = l_Lean_Elab_Command_getScope___redArg(v___y_2190_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v___x_2193_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_a_2192_);
lean_dec_ref_known(v___x_2191_, 1);
v___x_2193_ = l_Lean_Elab_Command_getScope___redArg(v___y_2190_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2228_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2196_ = v___x_2193_;
v_isShared_2197_ = v_isSharedCheck_2228_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2193_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2228_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2198_; lean_object* v_currNamespace_2199_; lean_object* v_openDecls_2200_; lean_object* v_env_2201_; lean_object* v_messages_2202_; lean_object* v_scopes_2203_; lean_object* v_usedQuotCtxts_2204_; lean_object* v_nextMacroScope_2205_; lean_object* v_maxRecDepth_2206_; lean_object* v_ngen_2207_; lean_object* v_auxDeclNGen_2208_; lean_object* v_infoState_2209_; lean_object* v_traceState_2210_; lean_object* v_snapshotTasks_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2227_; 
v___x_2198_ = lean_st_ref_take(v___y_2190_);
v_currNamespace_2199_ = lean_ctor_get(v_a_2192_, 2);
lean_inc(v_currNamespace_2199_);
lean_dec(v_a_2192_);
v_openDecls_2200_ = lean_ctor_get(v_a_2194_, 3);
lean_inc(v_openDecls_2200_);
lean_dec(v_a_2194_);
v_env_2201_ = lean_ctor_get(v___x_2198_, 0);
v_messages_2202_ = lean_ctor_get(v___x_2198_, 1);
v_scopes_2203_ = lean_ctor_get(v___x_2198_, 2);
v_usedQuotCtxts_2204_ = lean_ctor_get(v___x_2198_, 3);
v_nextMacroScope_2205_ = lean_ctor_get(v___x_2198_, 4);
v_maxRecDepth_2206_ = lean_ctor_get(v___x_2198_, 5);
v_ngen_2207_ = lean_ctor_get(v___x_2198_, 6);
v_auxDeclNGen_2208_ = lean_ctor_get(v___x_2198_, 7);
v_infoState_2209_ = lean_ctor_get(v___x_2198_, 8);
v_traceState_2210_ = lean_ctor_get(v___x_2198_, 9);
v_snapshotTasks_2211_ = lean_ctor_get(v___x_2198_, 10);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2213_ = v___x_2198_;
v_isShared_2214_ = v_isSharedCheck_2227_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_snapshotTasks_2211_);
lean_inc(v_traceState_2210_);
lean_inc(v_infoState_2209_);
lean_inc(v_auxDeclNGen_2208_);
lean_inc(v_ngen_2207_);
lean_inc(v_maxRecDepth_2206_);
lean_inc(v_nextMacroScope_2205_);
lean_inc(v_usedQuotCtxts_2204_);
lean_inc(v_scopes_2203_);
lean_inc(v_messages_2202_);
lean_inc(v_env_2201_);
lean_dec(v___x_2198_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2227_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2215_, 0, v_currNamespace_2199_);
lean_ctor_set(v___x_2215_, 1, v_openDecls_2200_);
v___x_2216_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
lean_ctor_set(v___x_2216_, 1, v___y_2184_);
lean_inc_ref(v___y_2188_);
lean_inc_ref(v___y_2189_);
v___x_2217_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2217_, 0, v___y_2189_);
lean_ctor_set(v___x_2217_, 1, v___y_2183_);
lean_ctor_set(v___x_2217_, 2, v___y_2186_);
lean_ctor_set(v___x_2217_, 3, v___y_2188_);
lean_ctor_set(v___x_2217_, 4, v___x_2216_);
lean_ctor_set_uint8(v___x_2217_, sizeof(void*)*5, v___y_2185_);
lean_ctor_set_uint8(v___x_2217_, sizeof(void*)*5 + 1, v___y_2187_);
lean_ctor_set_uint8(v___x_2217_, sizeof(void*)*5 + 2, v_isSilent_2178_);
v___x_2218_ = l_Lean_MessageLog_add(v___x_2217_, v_messages_2202_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 1, v___x_2218_);
v___x_2220_ = v___x_2213_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_env_2201_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v___x_2218_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_scopes_2203_);
lean_ctor_set(v_reuseFailAlloc_2226_, 3, v_usedQuotCtxts_2204_);
lean_ctor_set(v_reuseFailAlloc_2226_, 4, v_nextMacroScope_2205_);
lean_ctor_set(v_reuseFailAlloc_2226_, 5, v_maxRecDepth_2206_);
lean_ctor_set(v_reuseFailAlloc_2226_, 6, v_ngen_2207_);
lean_ctor_set(v_reuseFailAlloc_2226_, 7, v_auxDeclNGen_2208_);
lean_ctor_set(v_reuseFailAlloc_2226_, 8, v_infoState_2209_);
lean_ctor_set(v_reuseFailAlloc_2226_, 9, v_traceState_2210_);
lean_ctor_set(v_reuseFailAlloc_2226_, 10, v_snapshotTasks_2211_);
v___x_2220_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2221_ = lean_st_ref_set(v___y_2190_, v___x_2220_);
v___x_2222_ = lean_box(0);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 0, v___x_2222_);
v___x_2224_ = v___x_2196_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
}
else
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
lean_dec(v_a_2192_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2184_);
lean_dec_ref(v___y_2183_);
v_a_2229_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2231_ = v___x_2193_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2193_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2184_);
lean_dec_ref(v___y_2183_);
v_a_2237_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2191_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2191_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
v___jp_2245_:
{
lean_object* v_fileName_2251_; lean_object* v_fileMap_2252_; uint8_t v_suppressElabErrors_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2272_; 
v_fileName_2251_ = lean_ctor_get(v___y_2179_, 0);
v_fileMap_2252_ = lean_ctor_get(v___y_2179_, 1);
v_suppressElabErrors_2253_ = lean_ctor_get_uint8(v___y_2179_, sizeof(void*)*10);
v___x_2254_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2176_);
v___x_2255_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v___x_2254_, v___y_2180_);
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2258_ = v___x_2255_;
v_isShared_2259_ = v_isSharedCheck_2272_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2255_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2272_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
lean_inc_ref_n(v_fileMap_2252_, 2);
v___x_2260_ = l_Lean_FileMap_toPosition(v_fileMap_2252_, v___y_2247_);
lean_dec(v___y_2247_);
v___x_2261_ = l_Lean_FileMap_toPosition(v_fileMap_2252_, v___y_2250_);
lean_dec(v___y_2250_);
v___x_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
v___x_2263_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
if (v_suppressElabErrors_2253_ == 0)
{
lean_del_object(v___x_2258_);
v___y_2183_ = v___x_2260_;
v___y_2184_ = v_a_2256_;
v___y_2185_ = v___y_2248_;
v___y_2186_ = v___x_2262_;
v___y_2187_ = v___y_2249_;
v___y_2188_ = v___x_2263_;
v___y_2189_ = v_fileName_2251_;
v___y_2190_ = v___y_2180_;
goto v___jp_2182_;
}
else
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___f_2266_; uint8_t v___x_2267_; 
v___x_2264_ = lean_box(v___y_2246_);
v___x_2265_ = lean_box(v_suppressElabErrors_2253_);
v___f_2266_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2266_, 0, v___x_2264_);
lean_closure_set(v___f_2266_, 1, v___x_2265_);
lean_inc(v_a_2256_);
v___x_2267_ = l_Lean_MessageData_hasTag(v___f_2266_, v_a_2256_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; lean_object* v___x_2270_; 
lean_dec_ref_known(v___x_2262_, 1);
lean_dec_ref(v___x_2260_);
lean_dec(v_a_2256_);
v___x_2268_ = lean_box(0);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 0, v___x_2268_);
v___x_2270_ = v___x_2258_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2268_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
else
{
lean_del_object(v___x_2258_);
v___y_2183_ = v___x_2260_;
v___y_2184_ = v_a_2256_;
v___y_2185_ = v___y_2248_;
v___y_2186_ = v___x_2262_;
v___y_2187_ = v___y_2249_;
v___y_2188_ = v___x_2263_;
v___y_2189_ = v_fileName_2251_;
v___y_2190_ = v___y_2180_;
goto v___jp_2182_;
}
}
}
}
v___jp_2273_:
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_Syntax_getTailPos_x3f(v___y_2276_, v___y_2275_);
lean_dec(v___y_2276_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_inc(v___y_2278_);
v___y_2246_ = v___y_2274_;
v___y_2247_ = v___y_2278_;
v___y_2248_ = v___y_2275_;
v___y_2249_ = v___y_2277_;
v___y_2250_ = v___y_2278_;
goto v___jp_2245_;
}
else
{
lean_object* v_val_2280_; 
v_val_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_val_2280_);
lean_dec_ref_known(v___x_2279_, 1);
v___y_2246_ = v___y_2274_;
v___y_2247_ = v___y_2278_;
v___y_2248_ = v___y_2275_;
v___y_2249_ = v___y_2277_;
v___y_2250_ = v_val_2280_;
goto v___jp_2245_;
}
}
v___jp_2281_:
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Lean_Elab_Command_getRef___redArg(v___y_2179_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v_ref_2287_; lean_object* v___x_2288_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref_known(v___x_2285_, 1);
v_ref_2287_ = l_Lean_replaceRef(v_ref_2175_, v_a_2286_);
lean_dec(v_a_2286_);
v___x_2288_ = l_Lean_Syntax_getPos_x3f(v_ref_2287_, v___y_2283_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v___x_2289_; 
v___x_2289_ = lean_unsigned_to_nat(0u);
v___y_2274_ = v___y_2282_;
v___y_2275_ = v___y_2283_;
v___y_2276_ = v_ref_2287_;
v___y_2277_ = v___y_2284_;
v___y_2278_ = v___x_2289_;
goto v___jp_2273_;
}
else
{
lean_object* v_val_2290_; 
v_val_2290_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_val_2290_);
lean_dec_ref_known(v___x_2288_, 1);
v___y_2274_ = v___y_2282_;
v___y_2275_ = v___y_2283_;
v___y_2276_ = v_ref_2287_;
v___y_2277_ = v___y_2284_;
v___y_2278_ = v_val_2290_;
goto v___jp_2273_;
}
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec_ref(v_msgData_2176_);
v_a_2291_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2285_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2285_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
v___jp_2300_:
{
if (v___y_2303_ == 0)
{
v___y_2282_ = v___y_2301_;
v___y_2283_ = v___y_2302_;
v___y_2284_ = v_severity_2177_;
goto v___jp_2281_;
}
else
{
v___y_2282_ = v___y_2301_;
v___y_2283_ = v___y_2302_;
v___y_2284_ = v___x_2299_;
goto v___jp_2281_;
}
}
v___jp_2304_:
{
if (v___y_2305_ == 0)
{
lean_object* v___x_2306_; lean_object* v_scopes_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v_opts_2310_; uint8_t v___x_2311_; uint8_t v___x_2312_; 
v___x_2306_ = lean_st_ref_get(v___y_2180_);
v_scopes_2307_ = lean_ctor_get(v___x_2306_, 2);
lean_inc(v_scopes_2307_);
lean_dec(v___x_2306_);
v___x_2308_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2309_ = l_List_head_x21___redArg(v___x_2308_, v_scopes_2307_);
lean_dec(v_scopes_2307_);
v_opts_2310_ = lean_ctor_get(v___x_2309_, 1);
lean_inc_ref(v_opts_2310_);
lean_dec(v___x_2309_);
v___x_2311_ = 1;
v___x_2312_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2177_, v___x_2311_);
if (v___x_2312_ == 0)
{
lean_dec_ref(v_opts_2310_);
v___y_2301_ = v___y_2305_;
v___y_2302_ = v___y_2305_;
v___y_2303_ = v___x_2312_;
goto v___jp_2300_;
}
else
{
lean_object* v___x_2313_; uint8_t v___x_2314_; 
v___x_2313_ = l_Lean_warningAsError;
v___x_2314_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_2310_, v___x_2313_);
lean_dec_ref(v_opts_2310_);
v___y_2301_ = v___y_2305_;
v___y_2302_ = v___y_2305_;
v___y_2303_ = v___x_2314_;
goto v___jp_2300_;
}
}
else
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
lean_dec_ref(v_msgData_2176_);
v___x_2315_ = lean_box(0);
v___x_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
return v___x_2316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___boxed(lean_object* v_ref_2319_, lean_object* v_msgData_2320_, lean_object* v_severity_2321_, lean_object* v_isSilent_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
uint8_t v_severity_boxed_2326_; uint8_t v_isSilent_boxed_2327_; lean_object* v_res_2328_; 
v_severity_boxed_2326_ = lean_unbox(v_severity_2321_);
v_isSilent_boxed_2327_ = lean_unbox(v_isSilent_2322_);
v_res_2328_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_ref_2319_, v_msgData_2320_, v_severity_boxed_2326_, v_isSilent_boxed_2327_, v___y_2323_, v___y_2324_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v_ref_2319_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(lean_object* v_msgData_2329_, uint8_t v_severity_2330_, uint8_t v_isSilent_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v___x_2335_; 
v___x_2335_ = l_Lean_Elab_Command_getRef___redArg(v___y_2332_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2337_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref_known(v___x_2335_, 1);
v___x_2337_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_a_2336_, v_msgData_2329_, v_severity_2330_, v_isSilent_2331_, v___y_2332_, v___y_2333_);
lean_dec(v_a_2336_);
return v___x_2337_;
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec_ref(v_msgData_2329_);
v_a_2338_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2335_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2335_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26___boxed(lean_object* v_msgData_2346_, lean_object* v_severity_2347_, lean_object* v_isSilent_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
uint8_t v_severity_boxed_2352_; uint8_t v_isSilent_boxed_2353_; lean_object* v_res_2354_; 
v_severity_boxed_2352_ = lean_unbox(v_severity_2347_);
v_isSilent_boxed_2353_ = lean_unbox(v_isSilent_2348_);
v_res_2354_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_2346_, v_severity_boxed_2352_, v_isSilent_boxed_2353_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object* v_msgData_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
uint8_t v___x_2359_; uint8_t v___x_2360_; lean_object* v___x_2361_; 
v___x_2359_ = 0;
v___x_2360_ = 0;
v___x_2361_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_2355_, v___x_2359_, v___x_2360_, v___y_2356_, v___y_2357_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object* v_msgData_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v_msgData_2362_, v___y_2363_, v___y_2364_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object* v_init_2367_, lean_object* v_x_2368_){
_start:
{
if (lean_obj_tag(v_x_2368_) == 0)
{
lean_object* v_k_2370_; lean_object* v_v_2371_; lean_object* v_l_2372_; lean_object* v_r_2373_; lean_object* v___x_2374_; lean_object* v_a_2375_; lean_object* v_a_2376_; lean_object* v___x_2377_; 
v_k_2370_ = lean_ctor_get(v_x_2368_, 1);
lean_inc(v_k_2370_);
v_v_2371_ = lean_ctor_get(v_x_2368_, 2);
lean_inc(v_v_2371_);
v_l_2372_ = lean_ctor_get(v_x_2368_, 3);
lean_inc(v_l_2372_);
v_r_2373_ = lean_ctor_get(v_x_2368_, 4);
lean_inc(v_r_2373_);
lean_dec_ref_known(v_x_2368_, 5);
v___x_2374_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_2367_, v_l_2372_);
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref(v___x_2374_);
v_a_2376_ = lean_ctor_get(v_a_2375_, 0);
lean_inc(v_a_2376_);
lean_dec(v_a_2375_);
v___x_2377_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2370_, v_v_2371_, v_a_2376_);
v_init_2367_ = v___x_2377_;
v_x_2368_ = v_r_2373_;
goto _start;
}
else
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2379_, 0, v_init_2367_);
v___x_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
return v___x_2380_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object* v_init_2381_, lean_object* v_x_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_2381_, v_x_2382_);
return v_res_2384_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(uint8_t v___x_2385_, lean_object* v_x1_2386_, lean_object* v_x2_2387_){
_start:
{
lean_object* v_fst_2388_; lean_object* v_fst_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; 
v_fst_2388_ = lean_ctor_get(v_x1_2386_, 0);
lean_inc(v_fst_2388_);
lean_dec_ref(v_x1_2386_);
v_fst_2389_ = lean_ctor_get(v_x2_2387_, 0);
lean_inc(v_fst_2389_);
lean_dec_ref(v_x2_2387_);
v___x_2390_ = l_Lean_Name_toString(v_fst_2388_, v___x_2385_);
v___x_2391_ = l_Lean_Name_toString(v_fst_2389_, v___x_2385_);
v___x_2392_ = lean_string_dec_lt(v___x_2390_, v___x_2391_);
lean_dec_ref(v___x_2391_);
lean_dec_ref(v___x_2390_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0___boxed(lean_object* v___x_2393_, lean_object* v_x1_2394_, lean_object* v_x2_2395_){
_start:
{
uint8_t v___x_18311__boxed_2396_; uint8_t v_res_2397_; lean_object* v_r_2398_; 
v___x_18311__boxed_2396_ = lean_unbox(v___x_2393_);
v_res_2397_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_18311__boxed_2396_, v_x1_2394_, v_x2_2395_);
v_r_2398_ = lean_box(v_res_2397_);
return v_r_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(lean_object* v_hi_2399_, lean_object* v_pivot_2400_, lean_object* v_as_2401_, lean_object* v_i_2402_, lean_object* v_k_2403_){
_start:
{
uint8_t v___x_2404_; 
v___x_2404_ = lean_nat_dec_lt(v_k_2403_, v_hi_2399_);
if (v___x_2404_ == 0)
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
lean_dec(v_k_2403_);
lean_dec_ref(v_pivot_2400_);
v___x_2405_ = lean_array_fswap(v_as_2401_, v_i_2402_, v_hi_2399_);
v___x_2406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2406_, 0, v_i_2402_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
return v___x_2406_;
}
else
{
lean_object* v___x_2407_; lean_object* v_fst_2408_; lean_object* v_fst_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; 
v___x_2407_ = lean_array_fget_borrowed(v_as_2401_, v_k_2403_);
v_fst_2408_ = lean_ctor_get(v___x_2407_, 0);
v_fst_2409_ = lean_ctor_get(v_pivot_2400_, 0);
lean_inc(v_fst_2408_);
v___x_2410_ = l_Lean_Name_toString(v_fst_2408_, v___x_2404_);
lean_inc(v_fst_2409_);
v___x_2411_ = l_Lean_Name_toString(v_fst_2409_, v___x_2404_);
v___x_2412_ = lean_string_dec_lt(v___x_2410_, v___x_2411_);
lean_dec_ref(v___x_2411_);
lean_dec_ref(v___x_2410_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = lean_unsigned_to_nat(1u);
v___x_2414_ = lean_nat_add(v_k_2403_, v___x_2413_);
lean_dec(v_k_2403_);
v_k_2403_ = v___x_2414_;
goto _start;
}
else
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2416_ = lean_array_fswap(v_as_2401_, v_i_2402_, v_k_2403_);
v___x_2417_ = lean_unsigned_to_nat(1u);
v___x_2418_ = lean_nat_add(v_i_2402_, v___x_2417_);
lean_dec(v_i_2402_);
v___x_2419_ = lean_nat_add(v_k_2403_, v___x_2417_);
lean_dec(v_k_2403_);
v_as_2401_ = v___x_2416_;
v_i_2402_ = v___x_2418_;
v_k_2403_ = v___x_2419_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg___boxed(lean_object* v_hi_2421_, lean_object* v_pivot_2422_, lean_object* v_as_2423_, lean_object* v_i_2424_, lean_object* v_k_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_2421_, v_pivot_2422_, v_as_2423_, v_i_2424_, v_k_2425_);
lean_dec(v_hi_2421_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(lean_object* v_n_2427_, lean_object* v_as_2428_, lean_object* v_lo_2429_, lean_object* v_hi_2430_){
_start:
{
lean_object* v___y_2432_; uint8_t v___x_2442_; 
v___x_2442_ = lean_nat_dec_lt(v_lo_2429_, v_hi_2430_);
if (v___x_2442_ == 0)
{
lean_dec(v_lo_2429_);
return v_as_2428_;
}
else
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v_mid_2445_; lean_object* v___y_2447_; lean_object* v___y_2453_; lean_object* v___x_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; 
v___x_2443_ = lean_nat_add(v_lo_2429_, v_hi_2430_);
v___x_2444_ = lean_unsigned_to_nat(1u);
v_mid_2445_ = lean_nat_shiftr(v___x_2443_, v___x_2444_);
lean_dec(v___x_2443_);
v___x_2458_ = lean_array_fget_borrowed(v_as_2428_, v_mid_2445_);
v___x_2459_ = lean_array_fget_borrowed(v_as_2428_, v_lo_2429_);
lean_inc(v___x_2459_);
lean_inc(v___x_2458_);
v___x_2460_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2442_, v___x_2458_, v___x_2459_);
if (v___x_2460_ == 0)
{
v___y_2453_ = v_as_2428_;
goto v___jp_2452_;
}
else
{
lean_object* v___x_2461_; 
v___x_2461_ = lean_array_fswap(v_as_2428_, v_lo_2429_, v_mid_2445_);
v___y_2453_ = v___x_2461_;
goto v___jp_2452_;
}
v___jp_2446_:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; uint8_t v___x_2450_; 
v___x_2448_ = lean_array_fget_borrowed(v___y_2447_, v_mid_2445_);
v___x_2449_ = lean_array_fget_borrowed(v___y_2447_, v_hi_2430_);
lean_inc(v___x_2449_);
lean_inc(v___x_2448_);
v___x_2450_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2442_, v___x_2448_, v___x_2449_);
if (v___x_2450_ == 0)
{
lean_dec(v_mid_2445_);
v___y_2432_ = v___y_2447_;
goto v___jp_2431_;
}
else
{
lean_object* v___x_2451_; 
v___x_2451_ = lean_array_fswap(v___y_2447_, v_mid_2445_, v_hi_2430_);
lean_dec(v_mid_2445_);
v___y_2432_ = v___x_2451_;
goto v___jp_2431_;
}
}
v___jp_2452_:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; uint8_t v___x_2456_; 
v___x_2454_ = lean_array_fget_borrowed(v___y_2453_, v_hi_2430_);
v___x_2455_ = lean_array_fget_borrowed(v___y_2453_, v_lo_2429_);
lean_inc(v___x_2455_);
lean_inc(v___x_2454_);
v___x_2456_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2442_, v___x_2454_, v___x_2455_);
if (v___x_2456_ == 0)
{
v___y_2447_ = v___y_2453_;
goto v___jp_2446_;
}
else
{
lean_object* v___x_2457_; 
v___x_2457_ = lean_array_fswap(v___y_2453_, v_lo_2429_, v_hi_2430_);
v___y_2447_ = v___x_2457_;
goto v___jp_2446_;
}
}
}
v___jp_2431_:
{
lean_object* v_pivot_2433_; lean_object* v___x_2434_; lean_object* v_fst_2435_; lean_object* v_snd_2436_; uint8_t v___x_2437_; 
v_pivot_2433_ = lean_array_fget(v___y_2432_, v_hi_2430_);
lean_inc_n(v_lo_2429_, 2);
v___x_2434_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_2430_, v_pivot_2433_, v___y_2432_, v_lo_2429_, v_lo_2429_);
v_fst_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_fst_2435_);
v_snd_2436_ = lean_ctor_get(v___x_2434_, 1);
lean_inc(v_snd_2436_);
lean_dec_ref(v___x_2434_);
v___x_2437_ = lean_nat_dec_le(v_hi_2430_, v_fst_2435_);
if (v___x_2437_ == 0)
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2438_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_2427_, v_snd_2436_, v_lo_2429_, v_fst_2435_);
v___x_2439_ = lean_unsigned_to_nat(1u);
v___x_2440_ = lean_nat_add(v_fst_2435_, v___x_2439_);
lean_dec(v_fst_2435_);
v_as_2428_ = v___x_2438_;
v_lo_2429_ = v___x_2440_;
goto _start;
}
else
{
lean_dec(v_fst_2435_);
lean_dec(v_lo_2429_);
return v_snd_2436_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___boxed(lean_object* v_n_2462_, lean_object* v_as_2463_, lean_object* v_lo_2464_, lean_object* v_hi_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_2462_, v_as_2463_, v_lo_2464_, v_hi_2465_);
lean_dec(v_hi_2465_);
lean_dec(v_n_2462_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(lean_object* v_init_2467_, lean_object* v_x_2468_){
_start:
{
if (lean_obj_tag(v_x_2468_) == 0)
{
lean_object* v_k_2469_; lean_object* v_v_2470_; lean_object* v_l_2471_; lean_object* v_r_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v_k_2469_ = lean_ctor_get(v_x_2468_, 1);
v_v_2470_ = lean_ctor_get(v_x_2468_, 2);
v_l_2471_ = lean_ctor_get(v_x_2468_, 3);
v_r_2472_ = lean_ctor_get(v_x_2468_, 4);
v___x_2473_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_2467_, v_l_2471_);
lean_inc(v_v_2470_);
lean_inc(v_k_2469_);
v___x_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2474_, 0, v_k_2469_);
lean_ctor_set(v___x_2474_, 1, v_v_2470_);
v___x_2475_ = lean_array_push(v___x_2473_, v___x_2474_);
v_init_2467_ = v___x_2475_;
v_x_2468_ = v_r_2472_;
goto _start;
}
else
{
return v_init_2467_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25___boxed(lean_object* v_init_2477_, lean_object* v_x_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_2477_, v_x_2478_);
lean_dec(v_x_2478_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(lean_object* v_as_2480_, size_t v_sz_2481_, size_t v_i_2482_, lean_object* v_b_2483_){
_start:
{
uint8_t v___x_2485_; 
v___x_2485_ = lean_usize_dec_lt(v_i_2482_, v_sz_2481_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; 
v___x_2486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2486_, 0, v_b_2483_);
return v___x_2486_;
}
else
{
lean_object* v_a_2487_; lean_object* v_fst_2488_; lean_object* v_snd_2489_; lean_object* v_found_2490_; size_t v___x_2491_; size_t v___x_2492_; 
v_a_2487_ = lean_array_uget_borrowed(v_as_2480_, v_i_2482_);
v_fst_2488_ = lean_ctor_get(v_a_2487_, 0);
v_snd_2489_ = lean_ctor_get(v_a_2487_, 1);
lean_inc(v_snd_2489_);
lean_inc(v_fst_2488_);
v_found_2490_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2488_, v_snd_2489_, v_b_2483_);
v___x_2491_ = ((size_t)1ULL);
v___x_2492_ = lean_usize_add(v_i_2482_, v___x_2491_);
v_i_2482_ = v___x_2492_;
v_b_2483_ = v_found_2490_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg___boxed(lean_object* v_as_2494_, lean_object* v_sz_2495_, lean_object* v_i_2496_, lean_object* v_b_2497_, lean_object* v___y_2498_){
_start:
{
size_t v_sz_boxed_2499_; size_t v_i_boxed_2500_; lean_object* v_res_2501_; 
v_sz_boxed_2499_ = lean_unbox_usize(v_sz_2495_);
lean_dec(v_sz_2495_);
v_i_boxed_2500_ = lean_unbox_usize(v_i_2496_);
lean_dec(v_i_2496_);
v_res_2501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_2494_, v_sz_boxed_2499_, v_i_boxed_2500_, v_b_2497_);
lean_dec_ref(v_as_2494_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object* v_as_2502_, size_t v_sz_2503_, size_t v_i_2504_, lean_object* v_b_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
uint8_t v___x_2509_; 
v___x_2509_ = lean_usize_dec_lt(v_i_2504_, v_sz_2503_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; 
v___x_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2510_, 0, v_b_2505_);
return v___x_2510_;
}
else
{
lean_object* v_a_2511_; size_t v_sz_2512_; size_t v___x_2513_; lean_object* v___x_2514_; 
v_a_2511_ = lean_array_uget_borrowed(v_as_2502_, v_i_2504_);
v_sz_2512_ = lean_array_size(v_a_2511_);
v___x_2513_ = ((size_t)0ULL);
v___x_2514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_a_2511_, v_sz_2512_, v___x_2513_, v_b_2505_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; size_t v___x_2516_; size_t v___x_2517_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
lean_dec_ref_known(v___x_2514_, 1);
v___x_2516_ = ((size_t)1ULL);
v___x_2517_ = lean_usize_add(v_i_2504_, v___x_2516_);
v_i_2504_ = v___x_2517_;
v_b_2505_ = v_a_2515_;
goto _start;
}
else
{
return v___x_2514_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object* v_as_2519_, lean_object* v_sz_2520_, lean_object* v_i_2521_, lean_object* v_b_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
size_t v_sz_boxed_2526_; size_t v_i_boxed_2527_; lean_object* v_res_2528_; 
v_sz_boxed_2526_ = lean_unbox_usize(v_sz_2520_);
lean_dec(v_sz_2520_);
v_i_boxed_2527_ = lean_unbox_usize(v_i_2521_);
lean_dec(v_i_2521_);
v_res_2528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_as_2519_, v_sz_boxed_2526_, v_i_boxed_2527_, v_b_2522_, v___y_2523_, v___y_2524_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec_ref(v_as_2519_);
return v_res_2528_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = lean_box(1);
v___x_2530_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2529_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v___y_2537_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___x_2552_; lean_object* v_env_2553_; lean_object* v___x_2554_; lean_object* v_toEnvExtension_2555_; lean_object* v_asyncMode_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v_a_2562_; lean_object* v_a_2564_; lean_object* v_a_2587_; 
v___x_2552_ = lean_st_ref_get(v___y_2534_);
v_env_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc_ref_n(v_env_2553_, 2);
lean_dec(v___x_2552_);
v___x_2554_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2555_ = lean_ctor_get(v___x_2554_, 0);
v_asyncMode_2556_ = lean_ctor_get(v_toEnvExtension_2555_, 2);
v___x_2557_ = lean_box(1);
v___x_2558_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0, &l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0);
v___x_2559_ = lean_box(0);
v___x_2560_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2557_, v___x_2554_, v_env_2553_, v_asyncMode_2556_, v___x_2559_);
v___x_2561_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v___x_2557_, v___x_2560_);
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2562_);
lean_dec_ref(v___x_2561_);
v_a_2587_ = lean_ctor_get(v_a_2562_, 0);
lean_inc(v_a_2587_);
lean_dec(v_a_2562_);
v_a_2564_ = v_a_2587_;
goto v___jp_2563_;
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
v___x_2545_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v___y_2542_, v___y_2541_, v___y_2543_, v___y_2544_);
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
v___y_2541_ = v___y_2548_;
v___y_2542_ = v___y_2549_;
v___y_2543_ = v___y_2550_;
v___y_2544_ = v___y_2550_;
goto v___jp_2540_;
}
else
{
v___y_2541_ = v___y_2548_;
v___y_2542_ = v___y_2549_;
v___y_2543_ = v___y_2550_;
v___y_2544_ = v___y_2547_;
goto v___jp_2540_;
}
}
v___jp_2563_:
{
lean_object* v___x_2565_; lean_object* v_importedEntries_2566_; size_t v_sz_2567_; size_t v___x_2568_; lean_object* v___x_2569_; 
v___x_2565_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2558_, v_toEnvExtension_2555_, v_env_2553_, v_asyncMode_2556_, v___x_2559_);
v_importedEntries_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc_ref(v_importedEntries_2566_);
lean_dec(v___x_2565_);
v_sz_2567_ = lean_array_size(v_importedEntries_2566_);
v___x_2568_ = ((size_t)0ULL);
v___x_2569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_importedEntries_2566_, v_sz_2567_, v___x_2568_, v_a_2564_, v___y_2533_, v___y_2534_);
lean_dec_ref(v_importedEntries_2566_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v_arr_2573_; lean_object* v___x_2574_; uint8_t v___x_2575_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_a_2570_);
lean_dec_ref_known(v___x_2569_, 1);
v___x_2571_ = lean_unsigned_to_nat(0u);
v___x_2572_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1));
v_arr_2573_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v___x_2572_, v_a_2570_);
lean_dec(v_a_2570_);
v___x_2574_ = lean_array_get_size(v_arr_2573_);
v___x_2575_ = lean_nat_dec_eq(v___x_2574_, v___x_2571_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; 
v___x_2576_ = lean_unsigned_to_nat(1u);
v___x_2577_ = lean_nat_sub(v___x_2574_, v___x_2576_);
v___x_2578_ = lean_nat_dec_le(v___x_2571_, v___x_2577_);
if (v___x_2578_ == 0)
{
lean_inc(v___x_2577_);
v___y_2547_ = v___x_2577_;
v___y_2548_ = v_arr_2573_;
v___y_2549_ = v___x_2574_;
v___y_2550_ = v___x_2577_;
goto v___jp_2546_;
}
else
{
v___y_2547_ = v___x_2577_;
v___y_2548_ = v_arr_2573_;
v___y_2549_ = v___x_2574_;
v___y_2550_ = v___x_2571_;
goto v___jp_2546_;
}
}
else
{
v___y_2537_ = v_arr_2573_;
goto v___jp_2536_;
}
}
else
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
v_a_2579_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___x_2569_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2569_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2579_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
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
uint8_t v___x_2691_; 
v___x_2691_ = lean_nat_dec_le(v___x_2689_, v___x_2689_);
if (v___x_2691_ == 0)
{
if (v___x_2690_ == 0)
{
v___y_2682_ = v_b_2680_;
goto v___jp_2681_;
}
else
{
size_t v___x_2692_; size_t v___x_2693_; lean_object* v___x_2694_; 
v___x_2692_ = ((size_t)0ULL);
v___x_2693_ = lean_usize_of_nat(v___x_2689_);
v___x_2694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_2687_, v___x_2692_, v___x_2693_, v_b_2680_);
v___y_2682_ = v___x_2694_;
goto v___jp_2681_;
}
}
else
{
size_t v___x_2695_; size_t v___x_2696_; lean_object* v___x_2697_; 
v___x_2695_ = ((size_t)0ULL);
v___x_2696_ = lean_usize_of_nat(v___x_2689_);
v___x_2697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_2687_, v___x_2695_, v___x_2696_, v_b_2680_);
v___y_2682_ = v___x_2697_;
goto v___jp_2681_;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object* v_as_2698_, lean_object* v_i_2699_, lean_object* v_stop_2700_, lean_object* v_b_2701_){
_start:
{
size_t v_i_boxed_2702_; size_t v_stop_boxed_2703_; lean_object* v_res_2704_; 
v_i_boxed_2702_ = lean_unbox_usize(v_i_2699_);
lean_dec(v_i_2699_);
v_stop_boxed_2703_ = lean_unbox_usize(v_stop_2700_);
lean_dec(v_stop_2700_);
v_res_2704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v_as_2698_, v_i_boxed_2702_, v_stop_boxed_2703_, v_b_2701_);
lean_dec_ref(v_as_2698_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object* v___y_2705_){
_start:
{
lean_object* v___x_2707_; lean_object* v_env_2708_; lean_object* v___x_2709_; lean_object* v_ext_2710_; lean_object* v_toEnvExtension_2711_; lean_object* v_asyncMode_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v_categories_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2707_ = lean_st_ref_get(v___y_2705_);
v_env_2708_ = lean_ctor_get(v___x_2707_, 0);
lean_inc_ref_n(v_env_2708_, 2);
lean_dec(v___x_2707_);
v___x_2709_ = l_Lean_Parser_parserExtension;
v_ext_2710_ = lean_ctor_get(v___x_2709_, 1);
v_toEnvExtension_2711_ = lean_ctor_get(v_ext_2710_, 0);
v_asyncMode_2712_ = lean_ctor_get(v_toEnvExtension_2711_, 2);
v___x_2713_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2714_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2713_, v___x_2709_, v_env_2708_, v_asyncMode_2712_);
v_categories_2715_ = lean_ctor_get(v___x_2714_, 2);
lean_inc_ref(v_categories_2715_);
lean_dec(v___x_2714_);
v___x_2716_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_2717_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_2715_, v___x_2716_);
lean_dec_ref(v_categories_2715_);
if (lean_obj_tag(v___x_2717_) == 1)
{
lean_object* v_val_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2755_; 
v_val_2718_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2720_ = v___x_2717_;
v_isShared_2721_ = v_isSharedCheck_2755_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_val_2718_);
lean_dec(v___x_2717_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2755_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___y_2723_; lean_object* v___x_2732_; lean_object* v_toEnvExtension_2733_; lean_object* v_exportEntriesFn_2734_; lean_object* v_asyncMode_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v_importedEntries_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v_exported_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; uint8_t v___x_2747_; 
v___x_2732_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_2733_ = lean_ctor_get(v___x_2732_, 0);
v_exportEntriesFn_2734_ = lean_ctor_get(v___x_2732_, 4);
v_asyncMode_2735_ = lean_ctor_get(v_toEnvExtension_2733_, 2);
v___x_2736_ = lean_box(1);
v___x_2737_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_2738_ = lean_box(0);
lean_inc_ref_n(v_env_2708_, 2);
v___x_2739_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2737_, v_toEnvExtension_2733_, v_env_2708_, v_asyncMode_2735_, v___x_2738_);
v_importedEntries_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc_ref(v_importedEntries_2740_);
lean_dec(v___x_2739_);
v___x_2741_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2736_, v___x_2732_, v_env_2708_, v_asyncMode_2735_, v___x_2738_);
lean_inc_ref(v_exportEntriesFn_2734_);
v___x_2742_ = lean_apply_2(v_exportEntriesFn_2734_, v_env_2708_, v___x_2741_);
v_exported_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_exported_2743_);
lean_dec_ref(v___x_2742_);
v___x_2744_ = lean_array_push(v_importedEntries_2740_, v_exported_2743_);
v___x_2745_ = lean_unsigned_to_nat(0u);
v___x_2746_ = lean_array_get_size(v___x_2744_);
v___x_2747_ = lean_nat_dec_lt(v___x_2745_, v___x_2746_);
if (v___x_2747_ == 0)
{
lean_dec_ref(v___x_2744_);
v___y_2723_ = v___x_2736_;
goto v___jp_2722_;
}
else
{
uint8_t v___x_2748_; 
v___x_2748_ = lean_nat_dec_le(v___x_2746_, v___x_2746_);
if (v___x_2748_ == 0)
{
if (v___x_2747_ == 0)
{
lean_dec_ref(v___x_2744_);
v___y_2723_ = v___x_2736_;
goto v___jp_2722_;
}
else
{
size_t v___x_2749_; size_t v___x_2750_; lean_object* v___x_2751_; 
v___x_2749_ = ((size_t)0ULL);
v___x_2750_ = lean_usize_of_nat(v___x_2746_);
v___x_2751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_2744_, v___x_2749_, v___x_2750_, v___x_2736_);
lean_dec_ref(v___x_2744_);
v___y_2723_ = v___x_2751_;
goto v___jp_2722_;
}
}
else
{
size_t v___x_2752_; size_t v___x_2753_; lean_object* v___x_2754_; 
v___x_2752_ = ((size_t)0ULL);
v___x_2753_ = lean_usize_of_nat(v___x_2746_);
v___x_2754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_2744_, v___x_2752_, v___x_2753_, v___x_2736_);
lean_dec_ref(v___x_2744_);
v___y_2723_ = v___x_2754_;
goto v___jp_2722_;
}
}
v___jp_2722_:
{
lean_object* v_tables_2724_; lean_object* v_leadingTable_2725_; lean_object* v_trailingTable_2726_; lean_object* v_firstTokens_2727_; lean_object* v_firstTokens_2728_; lean_object* v___x_2730_; 
v_tables_2724_ = lean_ctor_get(v_val_2718_, 2);
v_leadingTable_2725_ = lean_ctor_get(v_tables_2724_, 0);
v_trailingTable_2726_ = lean_ctor_get(v_tables_2724_, 2);
lean_inc(v_trailingTable_2726_);
lean_inc(v_leadingTable_2725_);
lean_inc(v_val_2718_);
v_firstTokens_2727_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2718_, v_leadingTable_2725_, v___y_2723_);
v_firstTokens_2728_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2718_, v_trailingTable_2726_, v_firstTokens_2727_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set_tag(v___x_2720_, 0);
lean_ctor_set(v___x_2720_, 0, v_firstTokens_2728_);
v___x_2730_ = v___x_2720_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_firstTokens_2728_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
else
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
lean_dec(v___x_2717_);
lean_dec_ref(v_env_2708_);
v___x_2756_ = lean_box(1);
v___x_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2756_);
return v___x_2757_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_2758_);
lean_dec(v___y_2758_);
return v_res_2760_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0(void){
_start:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2761_ = lean_box(1);
v___x_2762_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2761_);
return v___x_2762_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2(void){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2764_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1));
v___x_2765_ = l_Lean_stringToMessageData(v___x_2764_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object* v_a_2766_, lean_object* v_a_2767_){
_start:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v_env_2772_; lean_object* v_env_2773_; lean_object* v_env_2774_; lean_object* v___x_2775_; lean_object* v_toEnvExtension_2776_; lean_object* v_exportEntriesFn_2777_; lean_object* v_asyncMode_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v_importedEntries_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2835_; 
v___x_2769_ = lean_st_ref_get(v_a_2767_);
v___x_2770_ = lean_st_ref_get(v_a_2767_);
v___x_2771_ = lean_st_ref_get(v_a_2767_);
v_env_2772_ = lean_ctor_get(v___x_2769_, 0);
lean_inc_ref(v_env_2772_);
lean_dec(v___x_2769_);
v_env_2773_ = lean_ctor_get(v___x_2770_, 0);
lean_inc_ref(v_env_2773_);
lean_dec(v___x_2770_);
v_env_2774_ = lean_ctor_get(v___x_2771_, 0);
lean_inc_ref(v_env_2774_);
lean_dec(v___x_2771_);
v___x_2775_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_2776_ = lean_ctor_get(v___x_2775_, 0);
v_exportEntriesFn_2777_ = lean_ctor_get(v___x_2775_, 4);
v_asyncMode_2778_ = lean_ctor_get(v_toEnvExtension_2776_, 2);
v___x_2779_ = lean_box(1);
v___x_2780_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_2781_ = lean_box(0);
v___x_2782_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2780_, v_toEnvExtension_2776_, v_env_2772_, v_asyncMode_2778_, v___x_2781_);
v_importedEntries_2783_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2835_ == 0)
{
lean_object* v_unused_2836_; 
v_unused_2836_ = lean_ctor_get(v___x_2782_, 1);
lean_dec(v_unused_2836_);
v___x_2785_ = v___x_2782_;
v_isShared_2786_ = v_isSharedCheck_2835_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_importedEntries_2783_);
lean_dec(v___x_2782_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2835_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v_exported_2789_; lean_object* v___x_2790_; size_t v_sz_2791_; size_t v___x_2792_; lean_object* v___x_2793_; 
v___x_2787_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2779_, v___x_2775_, v_env_2774_, v_asyncMode_2778_, v___x_2781_);
lean_inc_ref(v_exportEntriesFn_2777_);
v___x_2788_ = lean_apply_2(v_exportEntriesFn_2777_, v_env_2773_, v___x_2787_);
v_exported_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_exported_2789_);
lean_dec_ref(v___x_2788_);
v___x_2790_ = lean_array_push(v_importedEntries_2783_, v_exported_2789_);
v_sz_2791_ = lean_array_size(v___x_2790_);
v___x_2792_ = ((size_t)0ULL);
v___x_2793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v___x_2790_, v_sz_2791_, v___x_2792_, v___x_2779_, v_a_2766_, v_a_2767_);
lean_dec_ref(v___x_2790_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2795_; lean_object* v_a_2796_; lean_object* v___x_2797_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2794_);
lean_dec_ref_known(v___x_2793_, 1);
v___x_2795_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v_a_2767_);
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2796_);
lean_dec_ref(v___x_2795_);
v___x_2797_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v_a_2766_, v_a_2767_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
lean_dec_ref_known(v___x_2797_, 1);
v___x_2799_ = lean_box(0);
v___x_2800_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_2796_, v_a_2794_, v_a_2798_, v___x_2799_, v_a_2766_, v_a_2767_);
lean_dec(v_a_2794_);
lean_dec(v_a_2796_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2806_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_a_2801_);
lean_dec_ref_known(v___x_2800_, 1);
v___x_2802_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2);
v___x_2803_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2804_ = l_Lean_MessageData_joinSep(v_a_2801_, v___x_2803_);
if (v_isShared_2786_ == 0)
{
lean_ctor_set_tag(v___x_2785_, 7);
lean_ctor_set(v___x_2785_, 1, v___x_2804_);
lean_ctor_set(v___x_2785_, 0, v___x_2803_);
v___x_2806_ = v___x_2785_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v___x_2803_);
lean_ctor_set(v_reuseFailAlloc_2810_, 1, v___x_2804_);
v___x_2806_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2807_ = l_Lean_MessageData_nestD(v___x_2806_);
v___x_2808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2802_);
lean_ctor_set(v___x_2808_, 1, v___x_2807_);
v___x_2809_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v___x_2808_, v_a_2766_, v_a_2767_);
return v___x_2809_;
}
}
else
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
lean_del_object(v___x_2785_);
v_a_2811_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___x_2800_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2800_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec(v_a_2796_);
lean_dec(v_a_2794_);
lean_del_object(v___x_2785_);
v_a_2819_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2797_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2797_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_del_object(v___x_2785_);
v_a_2827_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2793_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2793_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2827_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_2837_, v_a_2838_);
lean_dec(v_a_2838_);
lean_dec_ref(v_a_2837_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object* v___stx_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_){
_start:
{
lean_object* v___x_2845_; 
v___x_2845_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_2842_, v_a_2843_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object* v___stx_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags(v___stx_2846_, v_a_2847_, v_a_2848_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
lean_dec(v___stx_2846_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object* v_00_u03b4_2851_, lean_object* v_t_2852_, lean_object* v_k_2853_, lean_object* v_fallback_2854_){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_2852_, v_k_2853_, v_fallback_2854_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object* v_00_u03b4_2856_, lean_object* v_t_2857_, lean_object* v_k_2858_, lean_object* v_fallback_2859_){
_start:
{
lean_object* v_res_2860_; 
v_res_2860_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(v_00_u03b4_2856_, v_t_2857_, v_k_2858_, v_fallback_2859_);
lean_dec(v_fallback_2859_);
lean_dec(v_k_2858_);
lean_dec(v_t_2857_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object* v_as_2861_, size_t v_sz_2862_, size_t v_i_2863_, lean_object* v_b_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
lean_object* v___x_2868_; 
v___x_2868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_2861_, v_sz_2862_, v_i_2863_, v_b_2864_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object* v_as_2869_, lean_object* v_sz_2870_, lean_object* v_i_2871_, lean_object* v_b_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
size_t v_sz_boxed_2876_; size_t v_i_boxed_2877_; lean_object* v_res_2878_; 
v_sz_boxed_2876_ = lean_unbox_usize(v_sz_2870_);
lean_dec(v_sz_2870_);
v_i_boxed_2877_ = lean_unbox_usize(v_i_2871_);
lean_dec(v_i_2871_);
v_res_2878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(v_as_2869_, v_sz_boxed_2876_, v_i_boxed_2877_, v_b_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec_ref(v_as_2869_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v___x_2882_; 
v___x_2882_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_2880_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(v___y_2883_, v___y_2884_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object* v_val_2887_, lean_object* v___x_2888_, lean_object* v___x_2889_, lean_object* v_inst_2890_, lean_object* v_R_2891_, lean_object* v_a_2892_, lean_object* v_b_2893_){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2887_, v___x_2888_, v___x_2889_, v_a_2892_, v_b_2893_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object* v_val_2895_, lean_object* v___x_2896_, lean_object* v___x_2897_, lean_object* v_inst_2898_, lean_object* v_R_2899_, lean_object* v_a_2900_, lean_object* v_b_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(v_val_2895_, v___x_2896_, v___x_2897_, v_inst_2898_, v_R_2899_, v_a_2900_, v_b_2901_);
lean_dec_ref(v___x_2896_);
lean_dec_ref(v_val_2895_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object* v_init_2903_, lean_object* v_t_2904_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_2903_, v_t_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object* v_n_2906_, lean_object* v_as_2907_, lean_object* v_lo_2908_, lean_object* v_hi_2909_, lean_object* v_w_2910_, lean_object* v_hlo_2911_, lean_object* v_hhi_2912_){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_2906_, v_as_2907_, v_lo_2908_, v_hi_2909_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object* v_n_2914_, lean_object* v_as_2915_, lean_object* v_lo_2916_, lean_object* v_hi_2917_, lean_object* v_w_2918_, lean_object* v_hlo_2919_, lean_object* v_hhi_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(v_n_2914_, v_as_2915_, v_lo_2916_, v_hi_2917_, v_w_2918_, v_hlo_2919_, v_hhi_2920_);
lean_dec(v_hi_2917_);
lean_dec(v_n_2914_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object* v_00_u03b2_2922_, lean_object* v_x_2923_, lean_object* v_x_2924_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_2923_, v_x_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2926_, lean_object* v_x_2927_, lean_object* v_x_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(v_00_u03b2_2926_, v_x_2927_, v_x_2928_);
lean_dec(v_x_2928_);
lean_dec_ref(v_x_2927_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object* v_tac_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_2930_, v___y_2932_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object* v_tac_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(v_tac_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object* v_00_u03b4_2940_, lean_object* v_t_2941_, lean_object* v_k_2942_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_2941_, v_k_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___boxed(lean_object* v_00_u03b4_2944_, lean_object* v_t_2945_, lean_object* v_k_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(v_00_u03b4_2944_, v_t_2945_, v_k_2946_);
lean_dec(v_k_2946_);
lean_dec(v_t_2945_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object* v_00_u03b2_2948_, lean_object* v_x_2949_, lean_object* v_x_2950_){
_start:
{
lean_object* v___x_2951_; 
v___x_2951_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_2949_, v_x_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object* v_00_u03b2_2952_, lean_object* v_x_2953_, lean_object* v_x_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(v_00_u03b2_2952_, v_x_2953_, v_x_2954_);
lean_dec(v_x_2954_);
lean_dec_ref(v_x_2953_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(lean_object* v_n_2956_, lean_object* v_lo_2957_, lean_object* v_hi_2958_, lean_object* v_hhi_2959_, lean_object* v_pivot_2960_, lean_object* v_as_2961_, lean_object* v_i_2962_, lean_object* v_k_2963_, lean_object* v_ilo_2964_, lean_object* v_ik_2965_, lean_object* v_w_2966_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_2958_, v_pivot_2960_, v_as_2961_, v_i_2962_, v_k_2963_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___boxed(lean_object* v_n_2968_, lean_object* v_lo_2969_, lean_object* v_hi_2970_, lean_object* v_hhi_2971_, lean_object* v_pivot_2972_, lean_object* v_as_2973_, lean_object* v_i_2974_, lean_object* v_k_2975_, lean_object* v_ilo_2976_, lean_object* v_ik_2977_, lean_object* v_w_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(v_n_2968_, v_lo_2969_, v_hi_2970_, v_hhi_2971_, v_pivot_2972_, v_as_2973_, v_i_2974_, v_k_2975_, v_ilo_2976_, v_ik_2977_, v_w_2978_);
lean_dec(v_hi_2970_);
lean_dec(v_lo_2969_);
lean_dec(v_n_2968_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(lean_object* v_as_2980_, size_t v_sz_2981_, size_t v_i_2982_, lean_object* v_b_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_2980_, v_sz_2981_, v_i_2982_, v_b_2983_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___boxed(lean_object* v_as_2988_, lean_object* v_sz_2989_, lean_object* v_i_2990_, lean_object* v_b_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
size_t v_sz_boxed_2995_; size_t v_i_boxed_2996_; lean_object* v_res_2997_; 
v_sz_boxed_2995_ = lean_unbox_usize(v_sz_2989_);
lean_dec(v_sz_2989_);
v_i_boxed_2996_ = lean_unbox_usize(v_i_2990_);
lean_dec(v_i_2990_);
v_res_2997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(v_as_2988_, v_sz_boxed_2995_, v_i_boxed_2996_, v_b_2991_, v___y_2992_, v___y_2993_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec_ref(v_as_2988_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object* v_init_2998_, lean_object* v_t_2999_){
_start:
{
lean_object* v___x_3000_; 
v___x_3000_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_2998_, v_t_2999_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object* v_init_3001_, lean_object* v_t_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(v_init_3001_, v_t_3002_);
lean_dec(v_t_3002_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object* v_n_3004_, lean_object* v_as_3005_, lean_object* v_lo_3006_, lean_object* v_hi_3007_, lean_object* v_w_3008_, lean_object* v_hlo_3009_, lean_object* v_hhi_3010_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_3004_, v_as_3005_, v_lo_3006_, v_hi_3007_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object* v_n_3012_, lean_object* v_as_3013_, lean_object* v_lo_3014_, lean_object* v_hi_3015_, lean_object* v_w_3016_, lean_object* v_hlo_3017_, lean_object* v_hhi_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(v_n_3012_, v_as_3013_, v_lo_3014_, v_hi_3015_, v_w_3016_, v_hlo_3017_, v_hhi_3018_);
lean_dec(v_hi_3015_);
lean_dec(v_n_3012_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object* v_init_3020_, lean_object* v_x_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v___x_3025_; 
v___x_3025_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_3020_, v_x_3021_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object* v_init_3026_, lean_object* v_x_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(v_init_3026_, v_x_3027_, v___y_3028_, v___y_3029_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_3032_, lean_object* v_x_3033_, size_t v_x_3034_, lean_object* v_x_3035_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3033_, v_x_3034_, v_x_3035_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3037_, lean_object* v_x_3038_, lean_object* v_x_3039_, lean_object* v_x_3040_){
_start:
{
size_t v_x_19039__boxed_3041_; lean_object* v_res_3042_; 
v_x_19039__boxed_3041_ = lean_unbox_usize(v_x_3039_);
lean_dec(v_x_3039_);
v_res_3042_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(v_00_u03b2_3037_, v_x_3038_, v_x_19039__boxed_3041_, v_x_3040_);
lean_dec(v_x_3040_);
lean_dec_ref(v_x_3038_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object* v_as_3043_, lean_object* v_k_3044_, lean_object* v_x_3045_, lean_object* v_x_3046_, lean_object* v_x_3047_){
_start:
{
lean_object* v___x_3048_; 
v___x_3048_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_3043_, v_k_3044_, v_x_3045_, v_x_3046_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object* v_as_3049_, lean_object* v_k_3050_, lean_object* v_x_3051_, lean_object* v_x_3052_, lean_object* v_x_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(v_as_3049_, v_k_3050_, v_x_3051_, v_x_3052_, v_x_3053_);
lean_dec_ref(v_k_3050_);
lean_dec_ref(v_as_3049_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(lean_object* v_00_u03b2_3055_, lean_object* v_m_3056_, lean_object* v_a_3057_){
_start:
{
lean_object* v___x_3058_; 
v___x_3058_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_3056_, v_a_3057_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___boxed(lean_object* v_00_u03b2_3059_, lean_object* v_m_3060_, lean_object* v_a_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(v_00_u03b2_3059_, v_m_3060_, v_a_3061_);
lean_dec(v_a_3061_);
lean_dec_ref(v_m_3060_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(lean_object* v_n_3063_, lean_object* v_lo_3064_, lean_object* v_hi_3065_, lean_object* v_hhi_3066_, lean_object* v_pivot_3067_, lean_object* v_as_3068_, lean_object* v_i_3069_, lean_object* v_k_3070_, lean_object* v_ilo_3071_, lean_object* v_ik_3072_, lean_object* v_w_3073_){
_start:
{
lean_object* v___x_3074_; 
v___x_3074_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_3065_, v_pivot_3067_, v_as_3068_, v_i_3069_, v_k_3070_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___boxed(lean_object* v_n_3075_, lean_object* v_lo_3076_, lean_object* v_hi_3077_, lean_object* v_hhi_3078_, lean_object* v_pivot_3079_, lean_object* v_as_3080_, lean_object* v_i_3081_, lean_object* v_k_3082_, lean_object* v_ilo_3083_, lean_object* v_ik_3084_, lean_object* v_w_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(v_n_3075_, v_lo_3076_, v_hi_3077_, v_hhi_3078_, v_pivot_3079_, v_as_3080_, v_i_3081_, v_k_3082_, v_ilo_3083_, v_ik_3084_, v_w_3085_);
lean_dec(v_hi_3077_);
lean_dec(v_lo_3076_);
lean_dec(v_n_3075_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_3087_, lean_object* v_keys_3088_, lean_object* v_vals_3089_, lean_object* v_heq_3090_, lean_object* v_i_3091_, lean_object* v_k_3092_){
_start:
{
lean_object* v___x_3093_; 
v___x_3093_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_3088_, v_vals_3089_, v_i_3091_, v_k_3092_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object* v_00_u03b2_3094_, lean_object* v_keys_3095_, lean_object* v_vals_3096_, lean_object* v_heq_3097_, lean_object* v_i_3098_, lean_object* v_k_3099_){
_start:
{
lean_object* v_res_3100_; 
v_res_3100_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(v_00_u03b2_3094_, v_keys_3095_, v_vals_3096_, v_heq_3097_, v_i_3098_, v_k_3099_);
lean_dec(v_k_3099_);
lean_dec_ref(v_vals_3096_);
lean_dec_ref(v_keys_3095_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(lean_object* v_00_u03b2_3101_, lean_object* v_a_3102_, lean_object* v_x_3103_){
_start:
{
lean_object* v___x_3104_; 
v___x_3104_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_3102_, v_x_3103_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___boxed(lean_object* v_00_u03b2_3105_, lean_object* v_a_3106_, lean_object* v_x_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(v_00_u03b2_3105_, v_a_3106_, v_x_3107_);
lean_dec(v_x_3107_);
lean_dec(v_a_3106_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1(){
_start:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3123_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3124_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1));
v___x_3125_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3126_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed), 4, 0);
v___x_3127_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3123_, v___x_3124_, v___x_3125_, v___x_3126_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object* v_a_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3(){
_start:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3132_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3133_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0));
v___x_3134_ = l_Lean_addBuiltinDocString(v___x_3132_, v___x_3133_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object* v_a_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5(){
_start:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3163_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3164_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6));
v___x_3165_ = l_Lean_addBuiltinDeclarationRanges(v___x_3163_, v___x_3164_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object* v_a_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object* v_env_3168_, lean_object* v___x_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, uint8_t v_includeUnnamed_3172_, lean_object* v_x_3173_, lean_object* v_____s_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
lean_object* v_fst_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3235_; 
v_fst_3180_ = lean_ctor_get(v_x_3173_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v_x_3173_);
if (v_isSharedCheck_3235_ == 0)
{
lean_object* v_unused_3236_; 
v_unused_3236_ = lean_ctor_get(v_x_3173_, 1);
lean_dec(v_unused_3236_);
v___x_3182_ = v_x_3173_;
v_isShared_3183_ = v_isSharedCheck_3235_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_fst_3180_);
lean_dec(v_x_3173_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3235_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v_userName_3185_; lean_object* v___y_3186_; lean_object* v___x_3220_; 
lean_inc(v_fst_3180_);
lean_inc_ref(v_env_3168_);
v___x_3220_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_3168_, v_fst_3180_);
if (lean_obj_tag(v___x_3220_) == 1)
{
lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3228_; 
lean_del_object(v___x_3182_);
lean_dec(v_fst_3180_);
lean_dec(v___x_3169_);
lean_dec_ref(v_env_3168_);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3228_ == 0)
{
lean_object* v_unused_3229_; 
v_unused_3229_ = lean_ctor_get(v___x_3220_, 0);
lean_dec(v_unused_3229_);
v___x_3222_ = v___x_3220_;
v_isShared_3223_ = v_isSharedCheck_3228_;
goto v_resetjp_3221_;
}
else
{
lean_dec(v___x_3220_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3228_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3225_; 
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 0, v_____s_3174_);
v___x_3225_ = v___x_3222_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_____s_3174_);
v___x_3225_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
lean_object* v___x_3226_; 
v___x_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3225_);
return v___x_3226_;
}
}
}
else
{
lean_object* v___x_3230_; 
lean_dec(v___x_3220_);
v___x_3230_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_a_3171_, v_fst_3180_);
if (lean_obj_tag(v___x_3230_) == 1)
{
lean_object* v_val_3231_; 
v_val_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_val_3231_);
lean_dec_ref_known(v___x_3230_, 1);
v_userName_3185_ = v_val_3231_;
v___y_3186_ = v___y_3177_;
goto v___jp_3184_;
}
else
{
lean_dec(v___x_3230_);
if (v_includeUnnamed_3172_ == 0)
{
lean_object* v___x_3232_; lean_object* v___x_3233_; 
lean_del_object(v___x_3182_);
lean_dec(v_fst_3180_);
lean_dec(v___x_3169_);
lean_dec_ref(v_env_3168_);
v___x_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3232_, 0, v_____s_3174_);
v___x_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3232_);
return v___x_3233_;
}
else
{
lean_object* v___x_3234_; 
lean_inc(v_fst_3180_);
v___x_3234_ = l_Lean_Name_toString(v_fst_3180_, v_includeUnnamed_3172_);
v_userName_3185_ = v___x_3234_;
v___y_3186_ = v___y_3177_;
goto v___jp_3184_;
}
}
}
v___jp_3184_:
{
uint8_t v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3187_ = 1;
v___x_3188_ = l_Lean_Options_empty;
v___x_3189_ = lean_box(0);
lean_inc(v_fst_3180_);
lean_inc_ref(v_env_3168_);
v___x_3190_ = l_Lean_findDocString_x3f(v_env_3168_, v_fst_3180_, v___x_3187_, v___x_3188_, v___x_3169_, v___x_3189_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3204_; 
lean_del_object(v___x_3182_);
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3193_ = v___x_3190_;
v_isShared_3194_ = v_isSharedCheck_3204_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3190_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3204_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3202_; 
v___x_3195_ = l_Lean_NameSet_empty;
v___x_3196_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_a_3170_, v_fst_3180_, v___x_3195_);
lean_inc(v_fst_3180_);
v___x_3197_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_3168_, v_fst_3180_);
v___x_3198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3198_, 0, v_fst_3180_);
lean_ctor_set(v___x_3198_, 1, v_userName_3185_);
lean_ctor_set(v___x_3198_, 2, v___x_3196_);
lean_ctor_set(v___x_3198_, 3, v_a_3191_);
lean_ctor_set(v___x_3198_, 4, v___x_3197_);
v___x_3199_ = lean_array_push(v_____s_3174_, v___x_3198_);
v___x_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3199_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 0, v___x_3200_);
v___x_3202_ = v___x_3193_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3200_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
else
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3219_; 
lean_dec_ref(v_userName_3185_);
lean_dec(v_fst_3180_);
lean_dec_ref(v_____s_3174_);
lean_dec_ref(v_env_3168_);
v_a_3205_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3207_ = v___x_3190_;
v_isShared_3208_ = v_isSharedCheck_3219_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3190_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3219_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v_ref_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3214_; 
v_ref_3209_ = lean_ctor_get(v___y_3186_, 5);
v___x_3210_ = lean_io_error_to_string(v_a_3205_);
v___x_3211_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3210_);
v___x_3212_ = l_Lean_MessageData_ofFormat(v___x_3211_);
lean_inc(v_ref_3209_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 1, v___x_3212_);
lean_ctor_set(v___x_3182_, 0, v_ref_3209_);
v___x_3214_ = v___x_3182_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_ref_3209_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v___x_3212_);
v___x_3214_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
lean_object* v___x_3216_; 
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 0, v___x_3214_);
v___x_3216_ = v___x_3207_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v___x_3214_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object* v_env_3237_, lean_object* v___x_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_includeUnnamed_3241_, lean_object* v_x_3242_, lean_object* v_____s_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
uint8_t v_includeUnnamed_boxed_3249_; lean_object* v_res_3250_; 
v_includeUnnamed_boxed_3249_ = lean_unbox(v_includeUnnamed_3241_);
v_res_3250_ = l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(v_env_3237_, v___x_3238_, v_a_3239_, v_a_3240_, v_includeUnnamed_boxed_3249_, v_x_3242_, v_____s_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v_a_3240_);
lean_dec(v_a_3239_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object* v_as_3251_, size_t v_sz_3252_, size_t v_i_3253_, lean_object* v_b_3254_){
_start:
{
uint8_t v___x_3256_; 
v___x_3256_ = lean_usize_dec_lt(v_i_3253_, v_sz_3252_);
if (v___x_3256_ == 0)
{
lean_object* v___x_3257_; 
v___x_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3257_, 0, v_b_3254_);
return v___x_3257_;
}
else
{
lean_object* v_a_3258_; lean_object* v_fst_3259_; lean_object* v_snd_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; size_t v___x_3265_; size_t v___x_3266_; 
v_a_3258_ = lean_array_uget_borrowed(v_as_3251_, v_i_3253_);
v_fst_3259_ = lean_ctor_get(v_a_3258_, 0);
v_snd_3260_ = lean_ctor_get(v_a_3258_, 1);
v___x_3261_ = l_Lean_NameSet_empty;
v___x_3262_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_3254_, v_fst_3259_, v___x_3261_);
lean_inc(v_snd_3260_);
v___x_3263_ = l_Lean_NameSet_insert(v___x_3262_, v_snd_3260_);
lean_inc(v_fst_3259_);
v___x_3264_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3259_, v___x_3263_, v_b_3254_);
v___x_3265_ = ((size_t)1ULL);
v___x_3266_ = lean_usize_add(v_i_3253_, v___x_3265_);
v_i_3253_ = v___x_3266_;
v_b_3254_ = v___x_3264_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object* v_as_3268_, lean_object* v_sz_3269_, lean_object* v_i_3270_, lean_object* v_b_3271_, lean_object* v___y_3272_){
_start:
{
size_t v_sz_boxed_3273_; size_t v_i_boxed_3274_; lean_object* v_res_3275_; 
v_sz_boxed_3273_ = lean_unbox_usize(v_sz_3269_);
lean_dec(v_sz_3269_);
v_i_boxed_3274_ = lean_unbox_usize(v_i_3270_);
lean_dec(v_i_3270_);
v_res_3275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_3268_, v_sz_boxed_3273_, v_i_boxed_3274_, v_b_3271_);
lean_dec_ref(v_as_3268_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object* v_as_3276_, size_t v_sz_3277_, size_t v_i_3278_, lean_object* v_b_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
uint8_t v___x_3285_; 
v___x_3285_ = lean_usize_dec_lt(v_i_3278_, v_sz_3277_);
if (v___x_3285_ == 0)
{
lean_object* v___x_3286_; 
v___x_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3286_, 0, v_b_3279_);
return v___x_3286_;
}
else
{
lean_object* v_a_3287_; size_t v_sz_3288_; size_t v___x_3289_; lean_object* v___x_3290_; 
v_a_3287_ = lean_array_uget_borrowed(v_as_3276_, v_i_3278_);
v_sz_3288_ = lean_array_size(v_a_3287_);
v___x_3289_ = ((size_t)0ULL);
v___x_3290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_a_3287_, v_sz_3288_, v___x_3289_, v_b_3279_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v_a_3291_; size_t v___x_3292_; size_t v___x_3293_; 
v_a_3291_ = lean_ctor_get(v___x_3290_, 0);
lean_inc(v_a_3291_);
lean_dec_ref_known(v___x_3290_, 1);
v___x_3292_ = ((size_t)1ULL);
v___x_3293_ = lean_usize_add(v_i_3278_, v___x_3292_);
v_i_3278_ = v___x_3293_;
v_b_3279_ = v_a_3291_;
goto _start;
}
else
{
return v___x_3290_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object* v_as_3295_, lean_object* v_sz_3296_, lean_object* v_i_3297_, lean_object* v_b_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
size_t v_sz_boxed_3304_; size_t v_i_boxed_3305_; lean_object* v_res_3306_; 
v_sz_boxed_3304_ = lean_unbox_usize(v_sz_3296_);
lean_dec(v_sz_3296_);
v_i_boxed_3305_ = lean_unbox_usize(v_i_3297_);
lean_dec(v_i_3297_);
v_res_3306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v_as_3295_, v_sz_boxed_3304_, v_i_boxed_3305_, v_b_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec_ref(v_as_3295_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object* v_f_3307_, lean_object* v_keys_3308_, lean_object* v_vals_3309_, lean_object* v_i_3310_, lean_object* v_acc_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v___x_3317_; uint8_t v___x_3318_; 
v___x_3317_ = lean_array_get_size(v_keys_3308_);
v___x_3318_ = lean_nat_dec_lt(v_i_3310_, v___x_3317_);
if (v___x_3318_ == 0)
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
lean_dec(v_i_3310_);
lean_dec_ref(v_f_3307_);
v___x_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3319_, 0, v_acc_3311_);
v___x_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3319_);
return v___x_3320_;
}
else
{
lean_object* v_k_3321_; lean_object* v_v_3322_; lean_object* v___x_3323_; 
v_k_3321_ = lean_array_fget_borrowed(v_keys_3308_, v_i_3310_);
v_v_3322_ = lean_array_fget_borrowed(v_vals_3309_, v_i_3310_);
lean_inc_ref(v_f_3307_);
lean_inc(v___y_3315_);
lean_inc_ref(v___y_3314_);
lean_inc(v___y_3313_);
lean_inc_ref(v___y_3312_);
lean_inc(v_v_3322_);
lean_inc(v_k_3321_);
v___x_3323_ = lean_apply_8(v_f_3307_, v_acc_3311_, v_k_3321_, v_v_3322_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, lean_box(0));
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3324_);
if (lean_obj_tag(v_a_3324_) == 0)
{
lean_dec_ref_known(v_a_3324_, 1);
lean_dec(v_i_3310_);
lean_dec_ref(v_f_3307_);
return v___x_3323_;
}
else
{
lean_object* v_a_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
lean_dec_ref_known(v___x_3323_, 1);
v_a_3325_ = lean_ctor_get(v_a_3324_, 0);
lean_inc(v_a_3325_);
lean_dec_ref_known(v_a_3324_, 1);
v___x_3326_ = lean_unsigned_to_nat(1u);
v___x_3327_ = lean_nat_add(v_i_3310_, v___x_3326_);
lean_dec(v_i_3310_);
v_i_3310_ = v___x_3327_;
v_acc_3311_ = v_a_3325_;
goto _start;
}
}
else
{
lean_dec(v_i_3310_);
lean_dec_ref(v_f_3307_);
return v___x_3323_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_f_3329_, lean_object* v_keys_3330_, lean_object* v_vals_3331_, lean_object* v_i_3332_, lean_object* v_acc_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3329_, v_keys_3330_, v_vals_3331_, v_i_3332_, v_acc_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec_ref(v_vals_3331_);
lean_dec_ref(v_keys_3330_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object* v_f_3340_, lean_object* v_x_3341_, lean_object* v_x_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
if (lean_obj_tag(v_x_3341_) == 0)
{
lean_object* v_es_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3370_; 
v_es_3348_ = lean_ctor_get(v_x_3341_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v_x_3341_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3350_ = v_x_3341_;
v_isShared_3351_ = v_isSharedCheck_3370_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_es_3348_);
lean_dec(v_x_3341_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3370_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; uint8_t v___x_3354_; 
v___x_3352_ = lean_unsigned_to_nat(0u);
v___x_3353_ = lean_array_get_size(v_es_3348_);
v___x_3354_ = lean_nat_dec_lt(v___x_3352_, v___x_3353_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3356_; 
lean_dec_ref(v_es_3348_);
lean_dec_ref(v_f_3340_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set_tag(v___x_3350_, 1);
lean_ctor_set(v___x_3350_, 0, v_x_3342_);
v___x_3356_ = v___x_3350_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_x_3342_);
v___x_3356_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
lean_object* v___x_3357_; 
v___x_3357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3356_);
return v___x_3357_;
}
}
else
{
uint8_t v___x_3359_; 
v___x_3359_ = lean_nat_dec_le(v___x_3353_, v___x_3353_);
if (v___x_3359_ == 0)
{
if (v___x_3354_ == 0)
{
lean_object* v___x_3361_; 
lean_dec_ref(v_es_3348_);
lean_dec_ref(v_f_3340_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set_tag(v___x_3350_, 1);
lean_ctor_set(v___x_3350_, 0, v_x_3342_);
v___x_3361_ = v___x_3350_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_x_3342_);
v___x_3361_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
lean_object* v___x_3362_; 
v___x_3362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3361_);
return v___x_3362_;
}
}
else
{
size_t v___x_3364_; size_t v___x_3365_; lean_object* v___x_3366_; 
lean_del_object(v___x_3350_);
v___x_3364_ = ((size_t)0ULL);
v___x_3365_ = lean_usize_of_nat(v___x_3353_);
v___x_3366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3340_, v_es_3348_, v___x_3364_, v___x_3365_, v_x_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
lean_dec_ref(v_es_3348_);
return v___x_3366_;
}
}
else
{
size_t v___x_3367_; size_t v___x_3368_; lean_object* v___x_3369_; 
lean_del_object(v___x_3350_);
v___x_3367_ = ((size_t)0ULL);
v___x_3368_ = lean_usize_of_nat(v___x_3353_);
v___x_3369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3340_, v_es_3348_, v___x_3367_, v___x_3368_, v_x_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
lean_dec_ref(v_es_3348_);
return v___x_3369_;
}
}
}
}
else
{
lean_object* v_ks_3371_; lean_object* v_vs_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v_ks_3371_ = lean_ctor_get(v_x_3341_, 0);
lean_inc_ref(v_ks_3371_);
v_vs_3372_ = lean_ctor_get(v_x_3341_, 1);
lean_inc_ref(v_vs_3372_);
lean_dec_ref_known(v_x_3341_, 2);
v___x_3373_ = lean_unsigned_to_nat(0u);
v___x_3374_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3340_, v_ks_3371_, v_vs_3372_, v___x_3373_, v_x_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
lean_dec_ref(v_vs_3372_);
lean_dec_ref(v_ks_3371_);
return v___x_3374_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_f_3375_, lean_object* v_as_3376_, size_t v_i_3377_, size_t v_stop_3378_, lean_object* v_b_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_){
_start:
{
lean_object* v_a_3386_; lean_object* v___y_3391_; uint8_t v___x_3394_; 
v___x_3394_ = lean_usize_dec_eq(v_i_3377_, v_stop_3378_);
if (v___x_3394_ == 0)
{
lean_object* v___x_3395_; 
v___x_3395_ = lean_array_uget_borrowed(v_as_3376_, v_i_3377_);
switch(lean_obj_tag(v___x_3395_))
{
case 0:
{
lean_object* v_key_3396_; lean_object* v_val_3397_; lean_object* v___x_3398_; 
v_key_3396_ = lean_ctor_get(v___x_3395_, 0);
v_val_3397_ = lean_ctor_get(v___x_3395_, 1);
lean_inc_ref(v_f_3375_);
lean_inc(v___y_3383_);
lean_inc_ref(v___y_3382_);
lean_inc(v___y_3381_);
lean_inc_ref(v___y_3380_);
lean_inc(v_val_3397_);
lean_inc(v_key_3396_);
v___x_3398_ = lean_apply_8(v_f_3375_, v_b_3379_, v_key_3396_, v_val_3397_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, lean_box(0));
v___y_3391_ = v___x_3398_;
goto v___jp_3390_;
}
case 1:
{
lean_object* v_node_3399_; lean_object* v___x_3400_; 
v_node_3399_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_node_3399_);
lean_inc_ref(v_f_3375_);
v___x_3400_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3375_, v_node_3399_, v_b_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_);
v___y_3391_ = v___x_3400_;
goto v___jp_3390_;
}
default: 
{
v_a_3386_ = v_b_3379_;
goto v___jp_3385_;
}
}
}
else
{
lean_object* v___x_3401_; lean_object* v___x_3402_; 
lean_dec_ref(v_f_3375_);
v___x_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3401_, 0, v_b_3379_);
v___x_3402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
return v___x_3402_;
}
v___jp_3385_:
{
size_t v___x_3387_; size_t v___x_3388_; 
v___x_3387_ = ((size_t)1ULL);
v___x_3388_ = lean_usize_add(v_i_3377_, v___x_3387_);
v_i_3377_ = v___x_3388_;
v_b_3379_ = v_a_3386_;
goto _start;
}
v___jp_3390_:
{
if (lean_obj_tag(v___y_3391_) == 0)
{
lean_object* v_a_3392_; 
v_a_3392_ = lean_ctor_get(v___y_3391_, 0);
if (lean_obj_tag(v_a_3392_) == 0)
{
lean_dec_ref(v_f_3375_);
return v___y_3391_;
}
else
{
lean_object* v_a_3393_; 
lean_inc_ref(v_a_3392_);
lean_dec_ref_known(v___y_3391_, 1);
v_a_3393_ = lean_ctor_get(v_a_3392_, 0);
lean_inc(v_a_3393_);
lean_dec_ref_known(v_a_3392_, 1);
v_a_3386_ = v_a_3393_;
goto v___jp_3385_;
}
}
else
{
lean_dec_ref(v_f_3375_);
return v___y_3391_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_3403_, lean_object* v_as_3404_, lean_object* v_i_3405_, lean_object* v_stop_3406_, lean_object* v_b_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
size_t v_i_boxed_3413_; size_t v_stop_boxed_3414_; lean_object* v_res_3415_; 
v_i_boxed_3413_ = lean_unbox_usize(v_i_3405_);
lean_dec(v_i_3405_);
v_stop_boxed_3414_ = lean_unbox_usize(v_stop_3406_);
lean_dec(v_stop_3406_);
v_res_3415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3403_, v_as_3404_, v_i_boxed_3413_, v_stop_boxed_3414_, v_b_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec_ref(v_as_3404_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_f_3416_, lean_object* v_x_3417_, lean_object* v_x_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
lean_object* v_res_3424_; 
v_res_3424_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3416_, v_x_3417_, v_x_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object* v_f_3425_, lean_object* v_s_3426_, lean_object* v_a_3427_, lean_object* v_b_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3434_, 0, v_a_3427_);
lean_ctor_set(v___x_3434_, 1, v_b_3428_);
lean_inc(v___y_3432_);
lean_inc_ref(v___y_3431_);
lean_inc(v___y_3430_);
lean_inc_ref(v___y_3429_);
v___x_3435_ = lean_apply_7(v_f_3425_, v___x_3434_, v_s_3426_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, lean_box(0));
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3462_; 
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3438_ = v___x_3435_;
v_isShared_3439_ = v_isSharedCheck_3462_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3435_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3462_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
if (lean_obj_tag(v_a_3436_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3450_; 
v_a_3440_ = lean_ctor_get(v_a_3436_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v_a_3436_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3442_ = v_a_3436_;
v_isShared_3443_ = v_isSharedCheck_3450_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v_a_3436_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3450_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3440_);
v___x_3445_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3447_; 
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 0, v___x_3445_);
v___x_3447_ = v___x_3438_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3445_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3461_; 
v_a_3451_ = lean_ctor_get(v_a_3436_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v_a_3436_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3453_ = v_a_3436_;
v_isShared_3454_ = v_isSharedCheck_3461_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v_a_3436_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3461_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_a_3451_);
v___x_3456_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
lean_object* v___x_3458_; 
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 0, v___x_3456_);
v___x_3458_ = v___x_3438_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v___x_3456_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
}
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
v_a_3463_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3435_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3435_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object* v_f_3471_, lean_object* v_s_3472_, lean_object* v_a_3473_, lean_object* v_b_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(v_f_3471_, v_s_3472_, v_a_3473_, v_b_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object* v_map_3481_, lean_object* v_init_3482_, lean_object* v_f_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_){
_start:
{
lean_object* v___f_3489_; lean_object* v___x_3490_; 
v___f_3489_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3489_, 0, v_f_3483_);
lean_inc_ref(v_map_3481_);
v___x_3490_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v___f_3489_, v_map_3481_, v_init_3482_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3499_; 
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3493_ = v___x_3490_;
v_isShared_3494_ = v_isSharedCheck_3499_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3490_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3499_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v_a_3495_; lean_object* v___x_3497_; 
v_a_3495_ = lean_ctor_get(v_a_3491_, 0);
lean_inc(v_a_3495_);
lean_dec(v_a_3491_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 0, v_a_3495_);
v___x_3497_ = v___x_3493_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_a_3495_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
else
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3507_; 
v_a_3500_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3502_ = v___x_3490_;
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3490_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
if (v_isShared_3503_ == 0)
{
v___x_3505_ = v___x_3502_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3500_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object* v_map_3508_, lean_object* v_init_3509_, lean_object* v_f_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_3508_, v_init_3509_, v_f_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec_ref(v_map_3508_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object* v___y_3517_){
_start:
{
lean_object* v___x_3519_; lean_object* v_env_3520_; lean_object* v___x_3521_; lean_object* v_ext_3522_; lean_object* v_toEnvExtension_3523_; lean_object* v_asyncMode_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v_categories_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3519_ = lean_st_ref_get(v___y_3517_);
v_env_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc_ref_n(v_env_3520_, 2);
lean_dec(v___x_3519_);
v___x_3521_ = l_Lean_Parser_parserExtension;
v_ext_3522_ = lean_ctor_get(v___x_3521_, 1);
v_toEnvExtension_3523_ = lean_ctor_get(v_ext_3522_, 0);
v_asyncMode_3524_ = lean_ctor_get(v_toEnvExtension_3523_, 2);
v___x_3525_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3526_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3525_, v___x_3521_, v_env_3520_, v_asyncMode_3524_);
v_categories_3527_ = lean_ctor_get(v___x_3526_, 2);
lean_inc_ref(v_categories_3527_);
lean_dec(v___x_3526_);
v___x_3528_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3529_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3527_, v___x_3528_);
lean_dec_ref(v_categories_3527_);
if (lean_obj_tag(v___x_3529_) == 1)
{
lean_object* v_val_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3567_; 
v_val_3530_ = lean_ctor_get(v___x_3529_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3529_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3532_ = v___x_3529_;
v_isShared_3533_ = v_isSharedCheck_3567_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_val_3530_);
lean_dec(v___x_3529_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3567_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___y_3535_; lean_object* v___x_3544_; lean_object* v_toEnvExtension_3545_; lean_object* v_exportEntriesFn_3546_; lean_object* v_asyncMode_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v_importedEntries_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v_exported_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; uint8_t v___x_3559_; 
v___x_3544_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3545_ = lean_ctor_get(v___x_3544_, 0);
v_exportEntriesFn_3546_ = lean_ctor_get(v___x_3544_, 4);
v_asyncMode_3547_ = lean_ctor_get(v_toEnvExtension_3545_, 2);
v___x_3548_ = lean_box(1);
v___x_3549_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3550_ = lean_box(0);
lean_inc_ref_n(v_env_3520_, 2);
v___x_3551_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3549_, v_toEnvExtension_3545_, v_env_3520_, v_asyncMode_3547_, v___x_3550_);
v_importedEntries_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc_ref(v_importedEntries_3552_);
lean_dec(v___x_3551_);
v___x_3553_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3548_, v___x_3544_, v_env_3520_, v_asyncMode_3547_, v___x_3550_);
lean_inc_ref(v_exportEntriesFn_3546_);
v___x_3554_ = lean_apply_2(v_exportEntriesFn_3546_, v_env_3520_, v___x_3553_);
v_exported_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_exported_3555_);
lean_dec_ref(v___x_3554_);
v___x_3556_ = lean_array_push(v_importedEntries_3552_, v_exported_3555_);
v___x_3557_ = lean_unsigned_to_nat(0u);
v___x_3558_ = lean_array_get_size(v___x_3556_);
v___x_3559_ = lean_nat_dec_lt(v___x_3557_, v___x_3558_);
if (v___x_3559_ == 0)
{
lean_dec_ref(v___x_3556_);
v___y_3535_ = v___x_3548_;
goto v___jp_3534_;
}
else
{
uint8_t v___x_3560_; 
v___x_3560_ = lean_nat_dec_le(v___x_3558_, v___x_3558_);
if (v___x_3560_ == 0)
{
if (v___x_3559_ == 0)
{
lean_dec_ref(v___x_3556_);
v___y_3535_ = v___x_3548_;
goto v___jp_3534_;
}
else
{
size_t v___x_3561_; size_t v___x_3562_; lean_object* v___x_3563_; 
v___x_3561_ = ((size_t)0ULL);
v___x_3562_ = lean_usize_of_nat(v___x_3558_);
v___x_3563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3556_, v___x_3561_, v___x_3562_, v___x_3548_);
lean_dec_ref(v___x_3556_);
v___y_3535_ = v___x_3563_;
goto v___jp_3534_;
}
}
else
{
size_t v___x_3564_; size_t v___x_3565_; lean_object* v___x_3566_; 
v___x_3564_ = ((size_t)0ULL);
v___x_3565_ = lean_usize_of_nat(v___x_3558_);
v___x_3566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3556_, v___x_3564_, v___x_3565_, v___x_3548_);
lean_dec_ref(v___x_3556_);
v___y_3535_ = v___x_3566_;
goto v___jp_3534_;
}
}
v___jp_3534_:
{
lean_object* v_tables_3536_; lean_object* v_leadingTable_3537_; lean_object* v_trailingTable_3538_; lean_object* v_firstTokens_3539_; lean_object* v_firstTokens_3540_; lean_object* v___x_3542_; 
v_tables_3536_ = lean_ctor_get(v_val_3530_, 2);
v_leadingTable_3537_ = lean_ctor_get(v_tables_3536_, 0);
v_trailingTable_3538_ = lean_ctor_get(v_tables_3536_, 2);
lean_inc(v_trailingTable_3538_);
lean_inc(v_leadingTable_3537_);
lean_inc(v_val_3530_);
v_firstTokens_3539_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3530_, v_leadingTable_3537_, v___y_3535_);
v_firstTokens_3540_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3530_, v_trailingTable_3538_, v_firstTokens_3539_);
if (v_isShared_3533_ == 0)
{
lean_ctor_set_tag(v___x_3532_, 0);
lean_ctor_set(v___x_3532_, 0, v_firstTokens_3540_);
v___x_3542_ = v___x_3532_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_firstTokens_3540_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
else
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
lean_dec(v___x_3529_);
lean_dec_ref(v_env_3520_);
v___x_3568_ = lean_box(1);
v___x_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3568_);
return v___x_3569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object* v___y_3570_, lean_object* v___y_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_3570_);
lean_dec(v___y_3570_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t v_includeUnnamed_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_){
_start:
{
lean_object* v___x_3581_; lean_object* v_env_3582_; lean_object* v___x_3583_; lean_object* v_toEnvExtension_3584_; lean_object* v_exportEntriesFn_3585_; lean_object* v_asyncMode_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v_importedEntries_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v_exported_3594_; lean_object* v___x_3595_; size_t v_sz_3596_; size_t v___x_3597_; lean_object* v___x_3598_; 
v___x_3581_ = lean_st_ref_get(v_a_3579_);
v_env_3582_ = lean_ctor_get(v___x_3581_, 0);
lean_inc_ref_n(v_env_3582_, 4);
lean_dec(v___x_3581_);
v___x_3583_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_3584_ = lean_ctor_get(v___x_3583_, 0);
v_exportEntriesFn_3585_ = lean_ctor_get(v___x_3583_, 4);
v_asyncMode_3586_ = lean_ctor_get(v_toEnvExtension_3584_, 2);
v___x_3587_ = lean_box(1);
v___x_3588_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_3589_ = lean_box(0);
v___x_3590_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3588_, v_toEnvExtension_3584_, v_env_3582_, v_asyncMode_3586_, v___x_3589_);
v_importedEntries_3591_ = lean_ctor_get(v___x_3590_, 0);
lean_inc_ref(v_importedEntries_3591_);
lean_dec(v___x_3590_);
v___x_3592_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3587_, v___x_3583_, v_env_3582_, v_asyncMode_3586_, v___x_3589_);
lean_inc_ref(v_exportEntriesFn_3585_);
v___x_3593_ = lean_apply_2(v_exportEntriesFn_3585_, v_env_3582_, v___x_3592_);
v_exported_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_exported_3594_);
lean_dec_ref(v___x_3593_);
v___x_3595_ = lean_array_push(v_importedEntries_3591_, v_exported_3594_);
v_sz_3596_ = lean_array_size(v___x_3595_);
v___x_3597_ = ((size_t)0ULL);
v___x_3598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v___x_3595_, v_sz_3596_, v___x_3597_, v___x_3587_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_);
lean_dec_ref(v___x_3595_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3623_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3601_ = v___x_3598_;
v_isShared_3602_ = v_isSharedCheck_3623_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3598_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3623_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3603_; lean_object* v_ext_3604_; lean_object* v_toEnvExtension_3605_; lean_object* v_asyncMode_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v_categories_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3603_ = l_Lean_Parser_parserExtension;
v_ext_3604_ = lean_ctor_get(v___x_3603_, 1);
v_toEnvExtension_3605_ = lean_ctor_get(v_ext_3604_, 0);
v_asyncMode_3606_ = lean_ctor_get(v_toEnvExtension_3605_, 2);
v___x_3607_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref(v_env_3582_);
v___x_3608_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3607_, v___x_3603_, v_env_3582_, v_asyncMode_3606_);
v_categories_3609_ = lean_ctor_get(v___x_3608_, 2);
lean_inc_ref(v_categories_3609_);
lean_dec(v___x_3608_);
v___x_3610_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0));
v___x_3611_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3612_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3609_, v___x_3611_);
lean_dec_ref(v_categories_3609_);
if (lean_obj_tag(v___x_3612_) == 1)
{
lean_object* v_val_3613_; lean_object* v___x_3614_; lean_object* v_a_3615_; lean_object* v_kinds_3616_; lean_object* v___x_3617_; lean_object* v___f_3618_; lean_object* v___x_3619_; 
lean_del_object(v___x_3601_);
v_val_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_val_3613_);
lean_dec_ref_known(v___x_3612_, 1);
v___x_3614_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v_a_3579_);
v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
lean_inc(v_a_3615_);
lean_dec_ref(v___x_3614_);
v_kinds_3616_ = lean_ctor_get(v_val_3613_, 1);
lean_inc_ref(v_kinds_3616_);
lean_dec(v_val_3613_);
v___x_3617_ = lean_box(v_includeUnnamed_3575_);
v___f_3618_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed), 12, 5);
lean_closure_set(v___f_3618_, 0, v_env_3582_);
lean_closure_set(v___f_3618_, 1, v___x_3589_);
lean_closure_set(v___f_3618_, 2, v_a_3599_);
lean_closure_set(v___f_3618_, 3, v_a_3615_);
lean_closure_set(v___f_3618_, 4, v___x_3617_);
v___x_3619_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_kinds_3616_, v___x_3610_, v___f_3618_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_);
lean_dec_ref(v_kinds_3616_);
return v___x_3619_;
}
else
{
lean_object* v___x_3621_; 
lean_dec(v___x_3612_);
lean_dec(v_a_3599_);
lean_dec_ref(v_env_3582_);
if (v_isShared_3602_ == 0)
{
lean_ctor_set(v___x_3601_, 0, v___x_3610_);
v___x_3621_ = v___x_3601_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3610_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_dec_ref(v_env_3582_);
v_a_3624_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3598_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3598_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object* v_includeUnnamed_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_){
_start:
{
uint8_t v_includeUnnamed_boxed_3638_; lean_object* v_res_3639_; 
v_includeUnnamed_boxed_3638_ = lean_unbox(v_includeUnnamed_3632_);
v_res_3639_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v_includeUnnamed_boxed_3638_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_);
lean_dec(v_a_3636_);
lean_dec_ref(v_a_3635_);
lean_dec(v_a_3634_);
lean_dec_ref(v_a_3633_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object* v_as_3640_, size_t v_sz_3641_, size_t v_i_3642_, lean_object* v_b_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
lean_object* v___x_3649_; 
v___x_3649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_3640_, v_sz_3641_, v_i_3642_, v_b_3643_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object* v_as_3650_, lean_object* v_sz_3651_, lean_object* v_i_3652_, lean_object* v_b_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
size_t v_sz_boxed_3659_; size_t v_i_boxed_3660_; lean_object* v_res_3661_; 
v_sz_boxed_3659_ = lean_unbox_usize(v_sz_3651_);
lean_dec(v_sz_3651_);
v_i_boxed_3660_ = lean_unbox_usize(v_i_3652_);
lean_dec(v_i_3652_);
v_res_3661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(v_as_3650_, v_sz_boxed_3659_, v_i_boxed_3660_, v_b_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
lean_dec(v___y_3655_);
lean_dec_ref(v___y_3654_);
lean_dec_ref(v_as_3650_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
lean_object* v___x_3667_; 
v___x_3667_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_3665_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
lean_object* v_res_3673_; 
v_res_3673_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object* v_00_u03c3_3674_, lean_object* v_00_u03b2_3675_, lean_object* v_map_3676_, lean_object* v_init_3677_, lean_object* v_f_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_){
_start:
{
lean_object* v___x_3684_; 
v___x_3684_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_3676_, v_init_3677_, v_f_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_);
return v___x_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object* v_00_u03c3_3685_, lean_object* v_00_u03b2_3686_, lean_object* v_map_3687_, lean_object* v_init_3688_, lean_object* v_f_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(v_00_u03c3_3685_, v_00_u03b2_3686_, v_map_3687_, v_init_3688_, v_f_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
lean_dec(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec_ref(v_map_3687_);
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object* v_map_3696_, lean_object* v_f_3697_, lean_object* v_init_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_){
_start:
{
lean_object* v___x_3704_; 
v___x_3704_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3697_, v_map_3696_, v_init_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_);
return v___x_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object* v_map_3705_, lean_object* v_f_3706_, lean_object* v_init_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(v_map_3705_, v_f_3706_, v_init_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object* v_00_u03c3_3714_, lean_object* v_00_u03c3_3715_, lean_object* v_00_u03b2_3716_, lean_object* v_map_3717_, lean_object* v_f_3718_, lean_object* v_init_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
lean_object* v___x_3725_; 
v___x_3725_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3718_, v_map_3717_, v_init_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
return v___x_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object* v_00_u03c3_3726_, lean_object* v_00_u03c3_3727_, lean_object* v_00_u03b2_3728_, lean_object* v_map_3729_, lean_object* v_f_3730_, lean_object* v_init_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(v_00_u03c3_3726_, v_00_u03c3_3727_, v_00_u03b2_3728_, v_map_3729_, v_f_3730_, v_init_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object* v_00_u03c3_3738_, lean_object* v_00_u03c3_3739_, lean_object* v_00_u03b1_3740_, lean_object* v_00_u03b2_3741_, lean_object* v_f_3742_, lean_object* v_x_3743_, lean_object* v_x_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_){
_start:
{
lean_object* v___x_3750_; 
v___x_3750_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3742_, v_x_3743_, v_x_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_);
return v___x_3750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03c3_3751_, lean_object* v_00_u03c3_3752_, lean_object* v_00_u03b1_3753_, lean_object* v_00_u03b2_3754_, lean_object* v_f_3755_, lean_object* v_x_3756_, lean_object* v_x_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(v_00_u03c3_3751_, v_00_u03c3_3752_, v_00_u03b1_3753_, v_00_u03b2_3754_, v_f_3755_, v_x_3756_, v_x_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_3764_, lean_object* v_00_u03b2_3765_, lean_object* v_00_u03c3_3766_, lean_object* v_00_u03c3_3767_, lean_object* v_f_3768_, lean_object* v_as_3769_, size_t v_i_3770_, size_t v_stop_3771_, lean_object* v_b_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
lean_object* v___x_3778_; 
v___x_3778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3768_, v_as_3769_, v_i_3770_, v_stop_3771_, v_b_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_);
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_3779_, lean_object* v_00_u03b2_3780_, lean_object* v_00_u03c3_3781_, lean_object* v_00_u03c3_3782_, lean_object* v_f_3783_, lean_object* v_as_3784_, lean_object* v_i_3785_, lean_object* v_stop_3786_, lean_object* v_b_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
size_t v_i_boxed_3793_; size_t v_stop_boxed_3794_; lean_object* v_res_3795_; 
v_i_boxed_3793_ = lean_unbox_usize(v_i_3785_);
lean_dec(v_i_3785_);
v_stop_boxed_3794_ = lean_unbox_usize(v_stop_3786_);
lean_dec(v_stop_3786_);
v_res_3795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_3779_, v_00_u03b2_3780_, v_00_u03c3_3781_, v_00_u03c3_3782_, v_f_3783_, v_as_3784_, v_i_boxed_3793_, v_stop_boxed_3794_, v_b_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec_ref(v_as_3784_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object* v_00_u03c3_3796_, lean_object* v_00_u03c3_3797_, lean_object* v_00_u03b1_3798_, lean_object* v_00_u03b2_3799_, lean_object* v_f_3800_, lean_object* v_keys_3801_, lean_object* v_vals_3802_, lean_object* v_heq_3803_, lean_object* v_i_3804_, lean_object* v_acc_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_){
_start:
{
lean_object* v___x_3811_; 
v___x_3811_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3800_, v_keys_3801_, v_vals_3802_, v_i_3804_, v_acc_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
return v___x_3811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03c3_3812_, lean_object* v_00_u03c3_3813_, lean_object* v_00_u03b1_3814_, lean_object* v_00_u03b2_3815_, lean_object* v_f_3816_, lean_object* v_keys_3817_, lean_object* v_vals_3818_, lean_object* v_heq_3819_, lean_object* v_i_3820_, lean_object* v_acc_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_){
_start:
{
lean_object* v_res_3827_; 
v_res_3827_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(v_00_u03c3_3812_, v_00_u03c3_3813_, v_00_u03b1_3814_, v_00_u03b2_3815_, v_f_3816_, v_keys_3817_, v_vals_3818_, v_heq_3819_, v_i_3820_, v_acc_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_dec_ref(v_vals_3818_);
lean_dec_ref(v_keys_3817_);
return v_res_3827_;
}
}
lean_object* runtime_initialize_Lean_DocString(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Doc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
