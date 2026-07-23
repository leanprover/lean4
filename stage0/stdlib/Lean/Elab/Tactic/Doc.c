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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
v___x_307_ = lean_st_ref_set(v___y_281_, v___x_306_);
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
v___y_281_ = v___y_316_;
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
v___x_323_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v___x_268_, v___x_322_, v___y_315_, v___y_316_);
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
v___y_315_ = v___y_325_;
v___y_316_ = v___y_326_;
v___y_317_ = v___x_270_;
goto v___jp_314_;
}
else
{
v___y_315_ = v___y_325_;
v___y_316_ = v___y_326_;
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
lean_dec(v_pre_485_);
lean_dec_ref_known(v_pre_484_, 2);
lean_dec_ref_known(v_kind_483_, 2);
lean_dec_ref_known(v___x_481_, 3);
goto v___jp_466_;
}
}
else
{
lean_dec_ref_known(v_kind_483_, 2);
lean_dec(v_pre_484_);
lean_dec_ref_known(v___x_481_, 3);
goto v___jp_466_;
}
}
else
{
lean_dec(v_kind_483_);
lean_dec_ref_known(v___x_481_, 3);
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
v___x_534_ = lean_st_ref_take(v___y_532_);
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
v___x_553_ = l_Lean_TSyntax_getId(v___y_531_);
lean_dec(v___y_531_);
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
v___x_561_ = lean_st_ref_set(v___y_532_, v___x_560_);
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
v___y_531_ = v_tag_571_;
v___y_532_ = v___y_569_;
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
v___y_531_ = v_tag_571_;
v___y_532_ = v___y_569_;
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
size_t v_x_4158__boxed_1052_; uint8_t v_res_1053_; lean_object* v_r_1054_; 
v_x_4158__boxed_1052_ = lean_unbox_usize(v_x_1050_);
lean_dec(v_x_1050_);
v_res_1053_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1049_, v_x_4158__boxed_1052_, v_x_1051_);
lean_dec(v_x_1051_);
lean_dec_ref(v_x_1049_);
v_r_1054_ = lean_box(v_res_1053_);
return v_r_1054_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1055_; uint64_t v___x_1056_; 
v___x_1055_ = lean_unsigned_to_nat(1723u);
v___x_1056_ = lean_uint64_of_nat(v___x_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(lean_object* v_x_1057_, lean_object* v_x_1058_){
_start:
{
uint64_t v___y_1060_; 
if (lean_obj_tag(v_x_1058_) == 0)
{
uint64_t v___x_1063_; 
v___x_1063_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1060_ = v___x_1063_;
goto v___jp_1059_;
}
else
{
uint64_t v_hash_1064_; 
v_hash_1064_ = lean_ctor_get_uint64(v_x_1058_, sizeof(void*)*2);
v___y_1060_ = v_hash_1064_;
goto v___jp_1059_;
}
v___jp_1059_:
{
size_t v___x_1061_; uint8_t v___x_1062_; 
v___x_1061_ = lean_uint64_to_usize(v___y_1060_);
v___x_1062_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1057_, v___x_1061_, v_x_1058_);
return v___x_1062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(lean_object* v_x_1065_, lean_object* v_x_1066_){
_start:
{
uint8_t v_res_1067_; lean_object* v_r_1068_; 
v_res_1067_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_1065_, v_x_1066_);
lean_dec(v_x_1066_);
lean_dec_ref(v_x_1065_);
v_r_1068_ = lean_box(v_res_1067_);
return v_r_1068_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(lean_object* v_tactics_1069_, lean_object* v_a_1070_, uint8_t v___x_1071_, lean_object* v_x_1072_, lean_object* v_____s_1073_){
_start:
{
lean_object* v_fst_1074_; lean_object* v_kinds_1075_; uint8_t v___x_1076_; 
v_fst_1074_ = lean_ctor_get(v_x_1072_, 0);
lean_inc(v_fst_1074_);
lean_dec_ref(v_x_1072_);
v_kinds_1075_ = lean_ctor_get(v_tactics_1069_, 1);
v___x_1076_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_kinds_1075_, v_fst_1074_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; 
lean_dec(v_fst_1074_);
lean_dec(v_a_1070_);
v___x_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1077_, 0, v_____s_1073_);
return v___x_1077_;
}
else
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1078_ = l_Lean_Name_toString(v_a_1070_, v___x_1071_);
v___x_1079_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1078_, v_fst_1074_, v_____s_1073_);
v___x_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
return v___x_1080_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(lean_object* v_tactics_1081_, lean_object* v_a_1082_, lean_object* v___x_1083_, lean_object* v_x_1084_, lean_object* v_____s_1085_){
_start:
{
uint8_t v___x_4220__boxed_1086_; lean_object* v_res_1087_; 
v___x_4220__boxed_1086_ = lean_unbox(v___x_1083_);
v_res_1087_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(v_tactics_1081_, v_a_1082_, v___x_4220__boxed_1086_, v_x_1084_, v_____s_1085_);
lean_dec_ref(v_tactics_1081_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_f_1088_, lean_object* v_keys_1089_, lean_object* v_vals_1090_, lean_object* v_i_1091_, lean_object* v_acc_1092_){
_start:
{
lean_object* v___x_1093_; uint8_t v___x_1094_; 
v___x_1093_ = lean_array_get_size(v_keys_1089_);
v___x_1094_ = lean_nat_dec_lt(v_i_1091_, v___x_1093_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; 
lean_dec(v_i_1091_);
lean_dec_ref(v_f_1088_);
v___x_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1095_, 0, v_acc_1092_);
return v___x_1095_;
}
else
{
lean_object* v_k_1096_; lean_object* v_v_1097_; lean_object* v___x_1098_; 
v_k_1096_ = lean_array_fget_borrowed(v_keys_1089_, v_i_1091_);
v_v_1097_ = lean_array_fget_borrowed(v_vals_1090_, v_i_1091_);
lean_inc_ref(v_f_1088_);
lean_inc(v_v_1097_);
lean_inc(v_k_1096_);
v___x_1098_ = lean_apply_3(v_f_1088_, v_acc_1092_, v_k_1096_, v_v_1097_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_dec(v_i_1091_);
lean_dec_ref(v_f_1088_);
return v___x_1098_;
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v___x_1098_, 1);
v___x_1100_ = lean_unsigned_to_nat(1u);
v___x_1101_ = lean_nat_add(v_i_1091_, v___x_1100_);
lean_dec(v_i_1091_);
v_i_1091_ = v___x_1101_;
v_acc_1092_ = v_a_1099_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_f_1103_, lean_object* v_keys_1104_, lean_object* v_vals_1105_, lean_object* v_i_1106_, lean_object* v_acc_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1103_, v_keys_1104_, v_vals_1105_, v_i_1106_, v_acc_1107_);
lean_dec_ref(v_vals_1105_);
lean_dec_ref(v_keys_1104_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object* v_f_1109_, lean_object* v_x_1110_, lean_object* v_x_1111_){
_start:
{
if (lean_obj_tag(v_x_1110_) == 0)
{
lean_object* v_es_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1132_; 
v_es_1112_ = lean_ctor_get(v_x_1110_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_x_1110_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1114_ = v_x_1110_;
v_isShared_1115_ = v_isSharedCheck_1132_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_es_1112_);
lean_dec(v_x_1110_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1132_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; 
v___x_1116_ = lean_unsigned_to_nat(0u);
v___x_1117_ = lean_array_get_size(v_es_1112_);
v___x_1118_ = lean_nat_dec_lt(v___x_1116_, v___x_1117_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1120_; 
lean_dec_ref(v_es_1112_);
lean_dec_ref(v_f_1109_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set_tag(v___x_1114_, 1);
lean_ctor_set(v___x_1114_, 0, v_x_1111_);
v___x_1120_ = v___x_1114_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_x_1111_);
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
uint8_t v___x_1122_; 
v___x_1122_ = lean_nat_dec_le(v___x_1117_, v___x_1117_);
if (v___x_1122_ == 0)
{
if (v___x_1118_ == 0)
{
lean_object* v___x_1124_; 
lean_dec_ref(v_es_1112_);
lean_dec_ref(v_f_1109_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set_tag(v___x_1114_, 1);
lean_ctor_set(v___x_1114_, 0, v_x_1111_);
v___x_1124_ = v___x_1114_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_x_1111_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
else
{
size_t v___x_1126_; size_t v___x_1127_; lean_object* v___x_1128_; 
lean_del_object(v___x_1114_);
v___x_1126_ = ((size_t)0ULL);
v___x_1127_ = lean_usize_of_nat(v___x_1117_);
v___x_1128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1109_, v_es_1112_, v___x_1126_, v___x_1127_, v_x_1111_);
lean_dec_ref(v_es_1112_);
return v___x_1128_;
}
}
else
{
size_t v___x_1129_; size_t v___x_1130_; lean_object* v___x_1131_; 
lean_del_object(v___x_1114_);
v___x_1129_ = ((size_t)0ULL);
v___x_1130_ = lean_usize_of_nat(v___x_1117_);
v___x_1131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1109_, v_es_1112_, v___x_1129_, v___x_1130_, v_x_1111_);
lean_dec_ref(v_es_1112_);
return v___x_1131_;
}
}
}
}
else
{
lean_object* v_ks_1133_; lean_object* v_vs_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v_ks_1133_ = lean_ctor_get(v_x_1110_, 0);
lean_inc_ref(v_ks_1133_);
v_vs_1134_ = lean_ctor_get(v_x_1110_, 1);
lean_inc_ref(v_vs_1134_);
lean_dec_ref_known(v_x_1110_, 2);
v___x_1135_ = lean_unsigned_to_nat(0u);
v___x_1136_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1109_, v_ks_1133_, v_vs_1134_, v___x_1135_, v_x_1111_);
lean_dec_ref(v_vs_1134_);
lean_dec_ref(v_ks_1133_);
return v___x_1136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_f_1137_, lean_object* v_as_1138_, size_t v_i_1139_, size_t v_stop_1140_, lean_object* v_b_1141_){
_start:
{
lean_object* v_a_1143_; lean_object* v___y_1148_; uint8_t v___x_1150_; 
v___x_1150_ = lean_usize_dec_eq(v_i_1139_, v_stop_1140_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_array_uget_borrowed(v_as_1138_, v_i_1139_);
switch(lean_obj_tag(v___x_1151_))
{
case 0:
{
lean_object* v_key_1152_; lean_object* v_val_1153_; lean_object* v___x_1154_; 
v_key_1152_ = lean_ctor_get(v___x_1151_, 0);
v_val_1153_ = lean_ctor_get(v___x_1151_, 1);
lean_inc_ref(v_f_1137_);
lean_inc(v_val_1153_);
lean_inc(v_key_1152_);
v___x_1154_ = lean_apply_3(v_f_1137_, v_b_1141_, v_key_1152_, v_val_1153_);
v___y_1148_ = v___x_1154_;
goto v___jp_1147_;
}
case 1:
{
lean_object* v_node_1155_; lean_object* v___x_1156_; 
v_node_1155_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_node_1155_);
lean_inc_ref(v_f_1137_);
v___x_1156_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1137_, v_node_1155_, v_b_1141_);
v___y_1148_ = v___x_1156_;
goto v___jp_1147_;
}
default: 
{
v_a_1143_ = v_b_1141_;
goto v___jp_1142_;
}
}
}
else
{
lean_object* v___x_1157_; 
lean_dec_ref(v_f_1137_);
v___x_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1157_, 0, v_b_1141_);
return v___x_1157_;
}
v___jp_1142_:
{
size_t v___x_1144_; size_t v___x_1145_; 
v___x_1144_ = ((size_t)1ULL);
v___x_1145_ = lean_usize_add(v_i_1139_, v___x_1144_);
v_i_1139_ = v___x_1145_;
v_b_1141_ = v_a_1143_;
goto _start;
}
v___jp_1147_:
{
if (lean_obj_tag(v___y_1148_) == 0)
{
lean_dec_ref(v_f_1137_);
return v___y_1148_;
}
else
{
lean_object* v_a_1149_; 
v_a_1149_ = lean_ctor_get(v___y_1148_, 0);
lean_inc(v_a_1149_);
lean_dec_ref_known(v___y_1148_, 1);
v_a_1143_ = v_a_1149_;
goto v___jp_1142_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_f_1158_, lean_object* v_as_1159_, lean_object* v_i_1160_, lean_object* v_stop_1161_, lean_object* v_b_1162_){
_start:
{
size_t v_i_boxed_1163_; size_t v_stop_boxed_1164_; lean_object* v_res_1165_; 
v_i_boxed_1163_ = lean_unbox_usize(v_i_1160_);
lean_dec(v_i_1160_);
v_stop_boxed_1164_ = lean_unbox_usize(v_stop_1161_);
lean_dec(v_stop_1161_);
v_res_1165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1158_, v_as_1159_, v_i_boxed_1163_, v_stop_boxed_1164_, v_b_1162_);
lean_dec_ref(v_as_1159_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0(lean_object* v_f_1166_, lean_object* v_s_1167_, lean_object* v_a_1168_, lean_object* v_b_1169_){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1170_, 0, v_a_1168_);
lean_ctor_set(v___x_1170_, 1, v_b_1169_);
v___x_1171_ = lean_apply_2(v_f_1166_, v___x_1170_, v_s_1167_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1171_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1171_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
v_a_1180_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1171_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1171_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(lean_object* v_map_1188_, lean_object* v_init_1189_, lean_object* v_f_1190_){
_start:
{
lean_object* v___f_1191_; lean_object* v___x_1192_; lean_object* v_a_1193_; 
v___f_1191_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1191_, 0, v_f_1190_);
lean_inc_ref(v_map_1188_);
v___x_1192_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v___f_1191_, v_map_1188_, v_init_1189_);
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_a_1193_);
lean_dec_ref(v___x_1192_);
return v_a_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___boxed(lean_object* v_map_1194_, lean_object* v_init_1195_, lean_object* v_f_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_1194_, v_init_1195_, v_f_1196_);
lean_dec_ref(v_map_1194_);
return v_res_1197_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1198_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0);
v___x_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(lean_object* v_tactics_1201_, lean_object* v_a_1202_, uint8_t v___x_1203_, lean_object* v_as_x27_1204_, lean_object* v_b_1205_){
_start:
{
if (lean_obj_tag(v_as_x27_1204_) == 0)
{
lean_dec(v_a_1202_);
lean_dec_ref(v_tactics_1201_);
return v_b_1205_;
}
else
{
lean_object* v_head_1206_; lean_object* v_fst_1207_; lean_object* v_info_1208_; lean_object* v_tail_1209_; lean_object* v_collectKinds_1210_; lean_object* v___x_1211_; lean_object* v___f_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v_head_1206_ = lean_ctor_get(v_as_x27_1204_, 0);
v_fst_1207_ = lean_ctor_get(v_head_1206_, 0);
v_info_1208_ = lean_ctor_get(v_fst_1207_, 0);
v_tail_1209_ = lean_ctor_get(v_as_x27_1204_, 1);
v_collectKinds_1210_ = lean_ctor_get(v_info_1208_, 1);
v___x_1211_ = lean_box(v___x_1203_);
lean_inc(v_a_1202_);
lean_inc_ref(v_tactics_1201_);
v___f_1212_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1212_, 0, v_tactics_1201_);
lean_closure_set(v___f_1212_, 1, v_a_1202_);
lean_closure_set(v___f_1212_, 2, v___x_1211_);
v___x_1213_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1);
lean_inc_ref(v_collectKinds_1210_);
v___x_1214_ = lean_apply_1(v_collectKinds_1210_, v___x_1213_);
v___x_1215_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v___x_1214_, v_b_1205_, v___f_1212_);
lean_dec_ref(v___x_1214_);
v_as_x27_1204_ = v_tail_1209_;
v_b_1205_ = v___x_1215_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(lean_object* v_tactics_1217_, lean_object* v_a_1218_, lean_object* v___x_1219_, lean_object* v_as_x27_1220_, lean_object* v_b_1221_){
_start:
{
uint8_t v___x_4394__boxed_1222_; lean_object* v_res_1223_; 
v___x_4394__boxed_1222_ = lean_unbox(v___x_1219_);
v_res_1223_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1217_, v_a_1218_, v___x_4394__boxed_1222_, v_as_x27_1220_, v_b_1221_);
lean_dec(v_as_x27_1220_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(lean_object* v_tactics_1227_, lean_object* v_init_1228_, lean_object* v_x_1229_){
_start:
{
if (lean_obj_tag(v_x_1229_) == 0)
{
lean_object* v_k_1230_; lean_object* v_v_1231_; lean_object* v_l_1232_; lean_object* v_r_1233_; lean_object* v___x_1234_; lean_object* v_a_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; 
v_k_1230_ = lean_ctor_get(v_x_1229_, 1);
lean_inc(v_k_1230_);
v_v_1231_ = lean_ctor_get(v_x_1229_, 2);
lean_inc(v_v_1231_);
v_l_1232_ = lean_ctor_get(v_x_1229_, 3);
lean_inc(v_l_1232_);
v_r_1233_ = lean_ctor_get(v_x_1229_, 4);
lean_inc(v_r_1233_);
lean_dec_ref_known(v_x_1229_, 5);
lean_inc_ref(v_tactics_1227_);
v___x_1234_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_1227_, v_init_1228_, v_l_1232_);
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
v___x_1236_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1));
v___x_1237_ = lean_name_eq(v_k_1230_, v___x_1236_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; 
lean_dec_ref(v___x_1234_);
lean_inc_ref(v_tactics_1227_);
v___x_1238_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1227_, v_k_1230_, v___x_1237_, v_v_1231_, v_a_1235_);
lean_dec(v_v_1231_);
v_init_1228_ = v___x_1238_;
v_x_1229_ = v_r_1233_;
goto _start;
}
else
{
lean_object* v_a_1240_; 
lean_dec(v_a_1235_);
lean_dec(v_v_1231_);
lean_dec(v_k_1230_);
v_a_1240_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1240_);
lean_dec_ref(v___x_1234_);
v_init_1228_ = v_a_1240_;
v_x_1229_ = v_r_1233_;
goto _start;
}
}
else
{
lean_object* v___x_1242_; 
lean_dec_ref(v_tactics_1227_);
v___x_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1242_, 0, v_init_1228_);
return v___x_1242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(lean_object* v_tactics_1243_, lean_object* v_table_1244_, lean_object* v_firsts_1245_){
_start:
{
lean_object* v___x_1246_; lean_object* v_a_1247_; 
v___x_1246_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_1243_, v_firsts_1245_, v_table_1244_);
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref(v___x_1246_);
return v_a_1247_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_object* v_00_u03b2_1248_, lean_object* v_x_1249_, lean_object* v_x_1250_){
_start:
{
uint8_t v___x_1251_; 
v___x_1251_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_1249_, v_x_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(lean_object* v_00_u03b2_1252_, lean_object* v_x_1253_, lean_object* v_x_1254_){
_start:
{
uint8_t v_res_1255_; lean_object* v_r_1256_; 
v_res_1255_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(v_00_u03b2_1252_, v_x_1253_, v_x_1254_);
lean_dec(v_x_1254_);
lean_dec_ref(v_x_1253_);
v_r_1256_ = lean_box(v_res_1255_);
return v_r_1256_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(lean_object* v___x_1257_, lean_object* v_k_1258_, lean_object* v_t_1259_, lean_object* v_hl_1260_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1257_, v_k_1258_, v_t_1259_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(lean_object* v_00_u03c3_1262_, lean_object* v_00_u03b2_1263_, lean_object* v_map_1264_, lean_object* v_init_1265_, lean_object* v_f_1266_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_1264_, v_init_1265_, v_f_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___boxed(lean_object* v_00_u03c3_1268_, lean_object* v_00_u03b2_1269_, lean_object* v_map_1270_, lean_object* v_init_1271_, lean_object* v_f_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(v_00_u03c3_1268_, v_00_u03b2_1269_, v_map_1270_, v_init_1271_, v_f_1272_);
lean_dec_ref(v_map_1270_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(lean_object* v_tactics_1274_, lean_object* v_a_1275_, uint8_t v___x_1276_, lean_object* v_as_1277_, lean_object* v_as_x27_1278_, lean_object* v_b_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1274_, v_a_1275_, v___x_1276_, v_as_x27_1278_, v_b_1279_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(lean_object* v_tactics_1282_, lean_object* v_a_1283_, lean_object* v___x_1284_, lean_object* v_as_1285_, lean_object* v_as_x27_1286_, lean_object* v_b_1287_, lean_object* v_a_1288_){
_start:
{
uint8_t v___x_4477__boxed_1289_; lean_object* v_res_1290_; 
v___x_4477__boxed_1289_ = lean_unbox(v___x_1284_);
v_res_1290_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(v_tactics_1282_, v_a_1283_, v___x_4477__boxed_1289_, v_as_1285_, v_as_x27_1286_, v_b_1287_, v_a_1288_);
lean_dec(v_as_x27_1286_);
lean_dec(v_as_1285_);
return v_res_1290_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_object* v_00_u03b2_1291_, lean_object* v_x_1292_, size_t v_x_1293_, lean_object* v_x_1294_){
_start:
{
uint8_t v___x_1295_; 
v___x_1295_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1292_, v_x_1293_, v_x_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1296_, lean_object* v_x_1297_, lean_object* v_x_1298_, lean_object* v_x_1299_){
_start:
{
size_t v_x_4486__boxed_1300_; uint8_t v_res_1301_; lean_object* v_r_1302_; 
v_x_4486__boxed_1300_ = lean_unbox_usize(v_x_1298_);
lean_dec(v_x_1298_);
v_res_1301_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(v_00_u03b2_1296_, v_x_1297_, v_x_4486__boxed_1300_, v_x_1299_);
lean_dec(v_x_1299_);
lean_dec_ref(v_x_1297_);
v_r_1302_ = lean_box(v_res_1301_);
return v_r_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(lean_object* v_map_1303_, lean_object* v_f_1304_, lean_object* v_init_1305_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1304_, v_map_1303_, v_init_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(lean_object* v_00_u03c3_1307_, lean_object* v_00_u03c3_1308_, lean_object* v_00_u03b2_1309_, lean_object* v_map_1310_, lean_object* v_f_1311_, lean_object* v_init_1312_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1311_, v_map_1310_, v_init_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1314_, lean_object* v_keys_1315_, lean_object* v_vals_1316_, lean_object* v_heq_1317_, lean_object* v_i_1318_, lean_object* v_k_1319_){
_start:
{
uint8_t v___x_1320_; 
v___x_1320_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_1315_, v_i_1318_, v_k_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1321_, lean_object* v_keys_1322_, lean_object* v_vals_1323_, lean_object* v_heq_1324_, lean_object* v_i_1325_, lean_object* v_k_1326_){
_start:
{
uint8_t v_res_1327_; lean_object* v_r_1328_; 
v_res_1327_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(v_00_u03b2_1321_, v_keys_1322_, v_vals_1323_, v_heq_1324_, v_i_1325_, v_k_1326_);
lean_dec(v_k_1326_);
lean_dec_ref(v_vals_1323_);
lean_dec_ref(v_keys_1322_);
v_r_1328_ = lean_box(v_res_1327_);
return v_r_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(lean_object* v_00_u03c3_1329_, lean_object* v_00_u03c3_1330_, lean_object* v_00_u03b1_1331_, lean_object* v_00_u03b2_1332_, lean_object* v_f_1333_, lean_object* v_x_1334_, lean_object* v_x_1335_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1333_, v_x_1334_, v_x_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b1_1337_, lean_object* v_00_u03b2_1338_, lean_object* v_00_u03c3_1339_, lean_object* v_00_u03c3_1340_, lean_object* v_f_1341_, lean_object* v_as_1342_, size_t v_i_1343_, size_t v_stop_1344_, lean_object* v_b_1345_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1341_, v_as_1342_, v_i_1343_, v_stop_1344_, v_b_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1347_, lean_object* v_00_u03b2_1348_, lean_object* v_00_u03c3_1349_, lean_object* v_00_u03c3_1350_, lean_object* v_f_1351_, lean_object* v_as_1352_, lean_object* v_i_1353_, lean_object* v_stop_1354_, lean_object* v_b_1355_){
_start:
{
size_t v_i_boxed_1356_; size_t v_stop_boxed_1357_; lean_object* v_res_1358_; 
v_i_boxed_1356_ = lean_unbox_usize(v_i_1353_);
lean_dec(v_i_1353_);
v_stop_boxed_1357_ = lean_unbox_usize(v_stop_1354_);
lean_dec(v_stop_1354_);
v_res_1358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(v_00_u03b1_1347_, v_00_u03b2_1348_, v_00_u03c3_1349_, v_00_u03c3_1350_, v_f_1351_, v_as_1352_, v_i_boxed_1356_, v_stop_boxed_1357_, v_b_1355_);
lean_dec_ref(v_as_1352_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03c3_1359_, lean_object* v_00_u03c3_1360_, lean_object* v_00_u03b1_1361_, lean_object* v_00_u03b2_1362_, lean_object* v_f_1363_, lean_object* v_keys_1364_, lean_object* v_vals_1365_, lean_object* v_heq_1366_, lean_object* v_i_1367_, lean_object* v_acc_1368_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1363_, v_keys_1364_, v_vals_1365_, v_i_1367_, v_acc_1368_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03c3_1370_, lean_object* v_00_u03c3_1371_, lean_object* v_00_u03b1_1372_, lean_object* v_00_u03b2_1373_, lean_object* v_f_1374_, lean_object* v_keys_1375_, lean_object* v_vals_1376_, lean_object* v_heq_1377_, lean_object* v_i_1378_, lean_object* v_acc_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(v_00_u03c3_1370_, v_00_u03c3_1371_, v_00_u03b1_1372_, v_00_u03b2_1373_, v_f_1374_, v_keys_1375_, v_vals_1376_, v_heq_1377_, v_i_1378_, v_acc_1379_);
lean_dec_ref(v_vals_1376_);
lean_dec_ref(v_keys_1375_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(lean_object* v_x1_1381_, lean_object* v_x2_1382_){
_start:
{
lean_object* v_fst_1383_; lean_object* v_snd_1384_; lean_object* v___x_1385_; 
v_fst_1383_ = lean_ctor_get(v_x2_1382_, 0);
lean_inc(v_fst_1383_);
v_snd_1384_ = lean_ctor_get(v_x2_1382_, 1);
lean_inc(v_snd_1384_);
lean_dec_ref(v_x2_1382_);
v___x_1385_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1383_, v_snd_1384_, v_x1_1381_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(lean_object* v___f_1405_, lean_object* v_x1_1406_, lean_object* v_x2_1407_){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; 
v___x_1408_ = lean_unsigned_to_nat(0u);
v___x_1409_ = lean_array_get_size(v_x2_1407_);
v___x_1410_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_1411_ = lean_nat_dec_lt(v___x_1408_, v___x_1409_);
if (v___x_1411_ == 0)
{
lean_dec_ref(v_x2_1407_);
lean_dec_ref(v___f_1405_);
return v_x1_1406_;
}
else
{
uint8_t v___x_1412_; 
v___x_1412_ = lean_nat_dec_le(v___x_1409_, v___x_1409_);
if (v___x_1412_ == 0)
{
if (v___x_1411_ == 0)
{
lean_dec_ref(v_x2_1407_);
lean_dec_ref(v___f_1405_);
return v_x1_1406_;
}
else
{
size_t v___x_1413_; size_t v___x_1414_; lean_object* v___x_1415_; 
v___x_1413_ = ((size_t)0ULL);
v___x_1414_ = lean_usize_of_nat(v___x_1409_);
v___x_1415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1410_, v___f_1405_, v_x2_1407_, v___x_1413_, v___x_1414_, v_x1_1406_);
return v___x_1415_;
}
}
else
{
size_t v___x_1416_; size_t v___x_1417_; lean_object* v___x_1418_; 
v___x_1416_ = ((size_t)0ULL);
v___x_1417_ = lean_usize_of_nat(v___x_1409_);
v___x_1418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1410_, v___f_1405_, v_x2_1407_, v___x_1416_, v___x_1417_, v_x1_1406_);
return v___x_1418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object* v___x_1422_, lean_object* v___x_1423_, lean_object* v___x_1424_, lean_object* v___x_1425_, lean_object* v___x_1426_, lean_object* v_toPure_1427_, lean_object* v___f_1428_, lean_object* v_env_1429_){
_start:
{
lean_object* v___x_1430_; lean_object* v_ext_1431_; lean_object* v_toEnvExtension_1432_; lean_object* v_asyncMode_1433_; lean_object* v___x_1434_; lean_object* v_categories_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1430_ = l_Lean_Parser_parserExtension;
v_ext_1431_ = lean_ctor_get(v___x_1430_, 1);
v_toEnvExtension_1432_ = lean_ctor_get(v_ext_1431_, 0);
v_asyncMode_1433_ = lean_ctor_get(v_toEnvExtension_1432_, 2);
lean_inc_ref(v_env_1429_);
v___x_1434_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1422_, v___x_1430_, v_env_1429_, v_asyncMode_1433_);
v_categories_1435_ = lean_ctor_get(v___x_1434_, 2);
lean_inc_ref(v_categories_1435_);
lean_dec(v___x_1434_);
v___x_1436_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_1437_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_1423_, v___x_1424_, v_categories_1435_, v___x_1436_);
lean_dec_ref(v_categories_1435_);
if (lean_obj_tag(v___x_1437_) == 1)
{
lean_object* v_val_1438_; lean_object* v___y_1440_; lean_object* v___x_1447_; lean_object* v_toEnvExtension_1448_; lean_object* v_exportEntriesFn_1449_; lean_object* v_asyncMode_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v_importedEntries_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v_exported_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
v_val_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_val_1438_);
lean_dec_ref_known(v___x_1437_, 1);
v___x_1447_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1448_ = lean_ctor_get(v___x_1447_, 0);
v_exportEntriesFn_1449_ = lean_ctor_get(v___x_1447_, 4);
v_asyncMode_1450_ = lean_ctor_get(v_toEnvExtension_1448_, 2);
v___x_1451_ = lean_box(0);
lean_inc_ref_n(v_env_1429_, 2);
v___x_1452_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1425_, v_toEnvExtension_1448_, v_env_1429_, v_asyncMode_1450_, v___x_1451_);
v_importedEntries_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc_ref(v_importedEntries_1453_);
lean_dec(v___x_1452_);
v___x_1454_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1426_, v___x_1447_, v_env_1429_, v_asyncMode_1450_, v___x_1451_);
lean_inc_ref(v_exportEntriesFn_1449_);
v___x_1455_ = lean_apply_2(v_exportEntriesFn_1449_, v_env_1429_, v___x_1454_);
v_exported_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_exported_1456_);
lean_dec_ref(v___x_1455_);
v___x_1457_ = lean_box(1);
v___x_1458_ = lean_array_push(v_importedEntries_1453_, v_exported_1456_);
v___x_1459_ = lean_unsigned_to_nat(0u);
v___x_1460_ = lean_array_get_size(v___x_1458_);
v___x_1461_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_1462_ = lean_nat_dec_lt(v___x_1459_, v___x_1460_);
if (v___x_1462_ == 0)
{
lean_dec_ref(v___x_1458_);
lean_dec_ref(v___f_1428_);
v___y_1440_ = v___x_1457_;
goto v___jp_1439_;
}
else
{
uint8_t v___x_1463_; 
v___x_1463_ = lean_nat_dec_le(v___x_1460_, v___x_1460_);
if (v___x_1463_ == 0)
{
if (v___x_1462_ == 0)
{
lean_dec_ref(v___x_1458_);
lean_dec_ref(v___f_1428_);
v___y_1440_ = v___x_1457_;
goto v___jp_1439_;
}
else
{
size_t v___x_1464_; size_t v___x_1465_; lean_object* v___x_1466_; 
v___x_1464_ = ((size_t)0ULL);
v___x_1465_ = lean_usize_of_nat(v___x_1460_);
v___x_1466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1461_, v___f_1428_, v___x_1458_, v___x_1464_, v___x_1465_, v___x_1457_);
v___y_1440_ = v___x_1466_;
goto v___jp_1439_;
}
}
else
{
size_t v___x_1467_; size_t v___x_1468_; lean_object* v___x_1469_; 
v___x_1467_ = ((size_t)0ULL);
v___x_1468_ = lean_usize_of_nat(v___x_1460_);
v___x_1469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1461_, v___f_1428_, v___x_1458_, v___x_1467_, v___x_1468_, v___x_1457_);
v___y_1440_ = v___x_1469_;
goto v___jp_1439_;
}
}
v___jp_1439_:
{
lean_object* v_tables_1441_; lean_object* v_leadingTable_1442_; lean_object* v_trailingTable_1443_; lean_object* v_firstTokens_1444_; lean_object* v_firstTokens_1445_; lean_object* v___x_1446_; 
v_tables_1441_ = lean_ctor_get(v_val_1438_, 2);
v_leadingTable_1442_ = lean_ctor_get(v_tables_1441_, 0);
v_trailingTable_1443_ = lean_ctor_get(v_tables_1441_, 2);
lean_inc(v_trailingTable_1443_);
lean_inc(v_leadingTable_1442_);
lean_inc(v_val_1438_);
v_firstTokens_1444_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_1438_, v_leadingTable_1442_, v___y_1440_);
v_firstTokens_1445_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_1438_, v_trailingTable_1443_, v_firstTokens_1444_);
v___x_1446_ = lean_apply_2(v_toPure_1427_, lean_box(0), v_firstTokens_1445_);
return v___x_1446_;
}
}
else
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_dec(v___x_1437_);
lean_dec_ref(v_env_1429_);
lean_dec_ref(v___f_1428_);
lean_dec(v___x_1426_);
v___x_1470_ = lean_box(1);
v___x_1471_ = lean_apply_2(v_toPure_1427_, lean_box(0), v___x_1470_);
return v___x_1471_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed(lean_object* v___x_1472_, lean_object* v___x_1473_, lean_object* v___x_1474_, lean_object* v___x_1475_, lean_object* v___x_1476_, lean_object* v_toPure_1477_, lean_object* v___f_1478_, lean_object* v_env_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(v___x_1472_, v___x_1473_, v___x_1474_, v___x_1475_, v___x_1476_, v_toPure_1477_, v___f_1478_, v_env_1479_);
lean_dec_ref(v___x_1475_);
lean_dec_ref(v___x_1472_);
return v_res_1480_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2(void){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = lean_box(1);
v___x_1485_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object* v_inst_1488_, lean_object* v_inst_1489_){
_start:
{
lean_object* v_toApplicative_1490_; lean_object* v_toBind_1491_; lean_object* v_getEnv_1492_; lean_object* v_toPure_1493_; lean_object* v___f_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___f_1500_; lean_object* v___x_1501_; 
v_toApplicative_1490_ = lean_ctor_get(v_inst_1488_, 0);
lean_inc_ref(v_toApplicative_1490_);
v_toBind_1491_ = lean_ctor_get(v_inst_1488_, 1);
lean_inc(v_toBind_1491_);
lean_dec_ref(v_inst_1488_);
v_getEnv_1492_ = lean_ctor_get(v_inst_1489_, 0);
lean_inc(v_getEnv_1492_);
lean_dec_ref(v_inst_1489_);
v_toPure_1493_ = lean_ctor_get(v_toApplicative_1490_, 1);
lean_inc(v_toPure_1493_);
lean_dec_ref(v_toApplicative_1490_);
v___f_1494_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1));
v___x_1495_ = lean_box(1);
v___x_1496_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_1497_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_1498_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___x_1499_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___f_1500_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1500_, 0, v___x_1499_);
lean_closure_set(v___f_1500_, 1, v___x_1497_);
lean_closure_set(v___f_1500_, 2, v___x_1498_);
lean_closure_set(v___f_1500_, 3, v___x_1496_);
lean_closure_set(v___f_1500_, 4, v___x_1495_);
lean_closure_set(v___f_1500_, 5, v_toPure_1493_);
lean_closure_set(v___f_1500_, 6, v___f_1494_);
v___x_1501_ = lean_apply_4(v_toBind_1491_, lean_box(0), lean_box(0), v_getEnv_1492_, v___f_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object* v_m_1502_, lean_object* v_inst_1503_, lean_object* v_inst_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(v_inst_1503_, v_inst_1504_);
return v___x_1505_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1506_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0);
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
return v___x_1508_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1509_ = lean_box(1);
v___x_1510_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4);
v___x_1511_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1);
v___x_1512_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
lean_ctor_set(v___x_1512_, 1, v___x_1510_);
lean_ctor_set(v___x_1512_, 2, v___x_1509_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object* v_n_1514_, lean_object* v___y_1515_, lean_object* v_toPure_1516_, lean_object* v_firsts_1517_, lean_object* v_____do__lift_1518_){
_start:
{
lean_object* v___y_1520_; lean_object* v_val_1531_; 
if (lean_obj_tag(v_____do__lift_1518_) == 0)
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__3));
lean_inc(v_n_1514_);
v___x_1534_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_1533_, v_firsts_1517_, v_n_1514_);
if (lean_obj_tag(v___x_1534_) == 0)
{
uint8_t v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1535_ = 1;
lean_inc(v_n_1514_);
v___x_1536_ = l_Lean_Name_toString(v_n_1514_, v___x_1535_);
v___x_1537_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
v___y_1520_ = v___x_1537_;
goto v___jp_1519_;
}
else
{
lean_object* v_val_1538_; 
v_val_1538_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_val_1538_);
lean_dec_ref_known(v___x_1534_, 1);
v_val_1531_ = v_val_1538_;
goto v___jp_1530_;
}
}
else
{
lean_object* v_val_1539_; 
lean_dec(v_firsts_1517_);
v_val_1539_ = lean_ctor_get(v_____do__lift_1518_, 0);
lean_inc(v_val_1539_);
lean_dec_ref_known(v_____do__lift_1518_, 1);
v_val_1531_ = v_val_1539_;
goto v___jp_1530_;
}
v___jp_1519_:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1521_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_1522_ = l_Lean_Expr_const___override(v_n_1514_, v___y_1515_);
v___x_1523_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2);
v___x_1524_ = lean_box(0);
v___x_1525_ = 0;
v___x_1526_ = l_Lean_MessageData_withExprHover(v___y_1520_, v___x_1522_, v___x_1523_, v___x_1524_, v___x_1524_, v___x_1524_, v___x_1525_);
v___x_1527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1521_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
v___x_1528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
lean_ctor_set(v___x_1528_, 1, v___x_1521_);
v___x_1529_ = lean_apply_2(v_toPure_1516_, lean_box(0), v___x_1528_);
return v___x_1529_;
}
v___jp_1530_:
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1532_, 0, v_val_1531_);
v___y_1520_ = v___x_1532_;
goto v___jp_1519_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object* v_n_1540_, lean_object* v_toPure_1541_, lean_object* v_firsts_1542_, lean_object* v_inst_1543_, lean_object* v_inst_1544_, lean_object* v_toBind_1545_, lean_object* v___x_1546_, lean_object* v___x_1547_, lean_object* v___f_1548_, lean_object* v_env_1549_){
_start:
{
lean_object* v___y_1551_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = l_Lean_Environment_constants(v_env_1549_);
lean_inc(v_n_1540_);
v___x_1556_ = l_Lean_SMap_find_x3f_x27___redArg(v___x_1546_, v___x_1547_, v___x_1555_, v_n_1540_);
lean_dec_ref(v___x_1555_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v___x_1557_; 
lean_dec_ref(v___f_1548_);
v___x_1557_ = lean_box(0);
v___y_1551_ = v___x_1557_;
goto v___jp_1550_;
}
else
{
lean_object* v_val_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v_val_1558_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_val_1558_);
lean_dec_ref_known(v___x_1556_, 1);
v___x_1559_ = l_Lean_ConstantInfo_levelParams(v_val_1558_);
lean_dec(v_val_1558_);
v___x_1560_ = lean_box(0);
v___x_1561_ = l_List_mapTR_loop___redArg(v___f_1548_, v___x_1559_, v___x_1560_);
v___y_1551_ = v___x_1561_;
goto v___jp_1550_;
}
v___jp_1550_:
{
lean_object* v___f_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
lean_inc(v_n_1540_);
v___f_1552_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1552_, 0, v_n_1540_);
lean_closure_set(v___f_1552_, 1, v___y_1551_);
lean_closure_set(v___f_1552_, 2, v_toPure_1541_);
lean_closure_set(v___f_1552_, 3, v_firsts_1542_);
v___x_1553_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(v_inst_1543_, v_inst_1544_, v_n_1540_);
v___x_1554_ = lean_apply_4(v_toBind_1545_, lean_box(0), lean_box(0), v___x_1553_, v___f_1552_);
return v___x_1554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object* v_inst_1563_, lean_object* v_inst_1564_, lean_object* v_firsts_1565_, lean_object* v_n_1566_){
_start:
{
lean_object* v_toApplicative_1567_; lean_object* v_toBind_1568_; lean_object* v_getEnv_1569_; lean_object* v_toPure_1570_; lean_object* v___f_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___f_1574_; lean_object* v___x_1575_; 
v_toApplicative_1567_ = lean_ctor_get(v_inst_1563_, 0);
v_toBind_1568_ = lean_ctor_get(v_inst_1563_, 1);
lean_inc_n(v_toBind_1568_, 2);
v_getEnv_1569_ = lean_ctor_get(v_inst_1564_, 0);
lean_inc(v_getEnv_1569_);
v_toPure_1570_ = lean_ctor_get(v_toApplicative_1567_, 1);
lean_inc(v_toPure_1570_);
v___f_1571_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0));
v___x_1572_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_1573_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___f_1574_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1574_, 0, v_n_1566_);
lean_closure_set(v___f_1574_, 1, v_toPure_1570_);
lean_closure_set(v___f_1574_, 2, v_firsts_1565_);
lean_closure_set(v___f_1574_, 3, v_inst_1563_);
lean_closure_set(v___f_1574_, 4, v_inst_1564_);
lean_closure_set(v___f_1574_, 5, v_toBind_1568_);
lean_closure_set(v___f_1574_, 6, v___x_1572_);
lean_closure_set(v___f_1574_, 7, v___x_1573_);
lean_closure_set(v___f_1574_, 8, v___f_1571_);
v___x_1575_ = lean_apply_4(v_toBind_1568_, lean_box(0), lean_box(0), v_getEnv_1569_, v___f_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object* v_m_1576_, lean_object* v_inst_1577_, lean_object* v_inst_1578_, lean_object* v_firsts_1579_, lean_object* v_n_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(v_inst_1577_, v_inst_1578_, v_firsts_1579_, v_n_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object* v_s_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0));
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object* v_s_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v_s_1586_);
lean_dec_ref(v_s_1586_);
return v_res_1587_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t v___x_1588_, lean_object* v_x1_1589_, lean_object* v_x2_1590_){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v___x_1591_ = l_Lean_Name_toString(v_x1_1589_, v___x_1588_);
v___x_1592_ = l_Lean_Name_toString(v_x2_1590_, v___x_1588_);
v___x_1593_ = lean_string_dec_lt(v___x_1591_, v___x_1592_);
lean_dec_ref(v___x_1592_);
lean_dec_ref(v___x_1591_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object* v___x_1594_, lean_object* v_x1_1595_, lean_object* v_x2_1596_){
_start:
{
uint8_t v___x_17042__boxed_1597_; uint8_t v_res_1598_; lean_object* v_r_1599_; 
v___x_17042__boxed_1597_ = lean_unbox(v___x_1594_);
v_res_1598_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_17042__boxed_1597_, v_x1_1595_, v_x2_1596_);
v_r_1599_ = lean_box(v_res_1598_);
return v_r_1599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(lean_object* v_hi_1600_, lean_object* v_pivot_1601_, lean_object* v_as_1602_, lean_object* v_i_1603_, lean_object* v_k_1604_){
_start:
{
uint8_t v___x_1605_; 
v___x_1605_ = lean_nat_dec_lt(v_k_1604_, v_hi_1600_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
lean_dec(v_k_1604_);
lean_dec(v_pivot_1601_);
v___x_1606_ = lean_array_fswap(v_as_1602_, v_i_1603_, v_hi_1600_);
v___x_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1607_, 0, v_i_1603_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
return v___x_1607_;
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; 
v___x_1608_ = lean_array_fget_borrowed(v_as_1602_, v_k_1604_);
lean_inc(v___x_1608_);
v___x_1609_ = l_Lean_Name_toString(v___x_1608_, v___x_1605_);
lean_inc(v_pivot_1601_);
v___x_1610_ = l_Lean_Name_toString(v_pivot_1601_, v___x_1605_);
v___x_1611_ = lean_string_dec_lt(v___x_1609_, v___x_1610_);
lean_dec_ref(v___x_1610_);
lean_dec_ref(v___x_1609_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = lean_unsigned_to_nat(1u);
v___x_1613_ = lean_nat_add(v_k_1604_, v___x_1612_);
lean_dec(v_k_1604_);
v_k_1604_ = v___x_1613_;
goto _start;
}
else
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1615_ = lean_array_fswap(v_as_1602_, v_i_1603_, v_k_1604_);
v___x_1616_ = lean_unsigned_to_nat(1u);
v___x_1617_ = lean_nat_add(v_i_1603_, v___x_1616_);
lean_dec(v_i_1603_);
v___x_1618_ = lean_nat_add(v_k_1604_, v___x_1616_);
lean_dec(v_k_1604_);
v_as_1602_ = v___x_1615_;
v_i_1603_ = v___x_1617_;
v_k_1604_ = v___x_1618_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg___boxed(lean_object* v_hi_1620_, lean_object* v_pivot_1621_, lean_object* v_as_1622_, lean_object* v_i_1623_, lean_object* v_k_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_1620_, v_pivot_1621_, v_as_1622_, v_i_1623_, v_k_1624_);
lean_dec(v_hi_1620_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object* v_n_1626_, lean_object* v_as_1627_, lean_object* v_lo_1628_, lean_object* v_hi_1629_){
_start:
{
lean_object* v___y_1631_; uint8_t v___x_1641_; 
v___x_1641_ = lean_nat_dec_lt(v_lo_1628_, v_hi_1629_);
if (v___x_1641_ == 0)
{
lean_dec(v_lo_1628_);
return v_as_1627_;
}
else
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v_mid_1644_; lean_object* v___y_1646_; lean_object* v___y_1652_; lean_object* v___x_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v___x_1642_ = lean_nat_add(v_lo_1628_, v_hi_1629_);
v___x_1643_ = lean_unsigned_to_nat(1u);
v_mid_1644_ = lean_nat_shiftr(v___x_1642_, v___x_1643_);
lean_dec(v___x_1642_);
v___x_1657_ = lean_array_fget_borrowed(v_as_1627_, v_mid_1644_);
v___x_1658_ = lean_array_fget_borrowed(v_as_1627_, v_lo_1628_);
lean_inc(v___x_1658_);
lean_inc(v___x_1657_);
v___x_1659_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1641_, v___x_1657_, v___x_1658_);
if (v___x_1659_ == 0)
{
v___y_1652_ = v_as_1627_;
goto v___jp_1651_;
}
else
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_array_fswap(v_as_1627_, v_lo_1628_, v_mid_1644_);
v___y_1652_ = v___x_1660_;
goto v___jp_1651_;
}
v___jp_1645_:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; 
v___x_1647_ = lean_array_fget_borrowed(v___y_1646_, v_mid_1644_);
v___x_1648_ = lean_array_fget_borrowed(v___y_1646_, v_hi_1629_);
lean_inc(v___x_1648_);
lean_inc(v___x_1647_);
v___x_1649_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1641_, v___x_1647_, v___x_1648_);
if (v___x_1649_ == 0)
{
lean_dec(v_mid_1644_);
v___y_1631_ = v___y_1646_;
goto v___jp_1630_;
}
else
{
lean_object* v___x_1650_; 
v___x_1650_ = lean_array_fswap(v___y_1646_, v_mid_1644_, v_hi_1629_);
lean_dec(v_mid_1644_);
v___y_1631_ = v___x_1650_;
goto v___jp_1630_;
}
}
v___jp_1651_:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1653_ = lean_array_fget_borrowed(v___y_1652_, v_hi_1629_);
v___x_1654_ = lean_array_fget_borrowed(v___y_1652_, v_lo_1628_);
lean_inc(v___x_1654_);
lean_inc(v___x_1653_);
v___x_1655_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1641_, v___x_1653_, v___x_1654_);
if (v___x_1655_ == 0)
{
v___y_1646_ = v___y_1652_;
goto v___jp_1645_;
}
else
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_array_fswap(v___y_1652_, v_lo_1628_, v_hi_1629_);
v___y_1646_ = v___x_1656_;
goto v___jp_1645_;
}
}
}
v___jp_1630_:
{
lean_object* v_pivot_1632_; lean_object* v___x_1633_; lean_object* v_fst_1634_; lean_object* v_snd_1635_; uint8_t v___x_1636_; 
v_pivot_1632_ = lean_array_fget(v___y_1631_, v_hi_1629_);
lean_inc_n(v_lo_1628_, 2);
v___x_1633_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_1629_, v_pivot_1632_, v___y_1631_, v_lo_1628_, v_lo_1628_);
v_fst_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_fst_1634_);
v_snd_1635_ = lean_ctor_get(v___x_1633_, 1);
lean_inc(v_snd_1635_);
lean_dec_ref(v___x_1633_);
v___x_1636_ = lean_nat_dec_le(v_hi_1629_, v_fst_1634_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1637_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_1626_, v_snd_1635_, v_lo_1628_, v_fst_1634_);
v___x_1638_ = lean_unsigned_to_nat(1u);
v___x_1639_ = lean_nat_add(v_fst_1634_, v___x_1638_);
lean_dec(v_fst_1634_);
v_as_1627_ = v___x_1637_;
v_lo_1628_ = v___x_1639_;
goto _start;
}
else
{
lean_dec(v_fst_1634_);
lean_dec(v_lo_1628_);
return v_snd_1635_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object* v_n_1661_, lean_object* v_as_1662_, lean_object* v_lo_1663_, lean_object* v_hi_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_1661_, v_as_1662_, v_lo_1663_, v_hi_1664_);
lean_dec(v_hi_1664_);
lean_dec(v_n_1661_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(lean_object* v_init_1666_, lean_object* v_x_1667_){
_start:
{
if (lean_obj_tag(v_x_1667_) == 0)
{
lean_object* v_k_1668_; lean_object* v_l_1669_; lean_object* v_r_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v_k_1668_ = lean_ctor_get(v_x_1667_, 1);
lean_inc(v_k_1668_);
v_l_1669_ = lean_ctor_get(v_x_1667_, 3);
lean_inc(v_l_1669_);
v_r_1670_ = lean_ctor_get(v_x_1667_, 4);
lean_inc(v_r_1670_);
lean_dec_ref_known(v_x_1667_, 5);
v___x_1671_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_1666_, v_l_1669_);
v___x_1672_ = lean_array_push(v___x_1671_, v_k_1668_);
v_init_1666_ = v___x_1672_;
v_x_1667_ = v_r_1670_;
goto _start;
}
else
{
return v_init_1666_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
if (lean_obj_tag(v_a_1674_) == 0)
{
lean_object* v___x_1676_; 
v___x_1676_ = l_List_reverse___redArg(v_a_1675_);
return v___x_1676_;
}
else
{
lean_object* v_head_1677_; lean_object* v_tail_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1687_; 
v_head_1677_ = lean_ctor_get(v_a_1674_, 0);
v_tail_1678_ = lean_ctor_get(v_a_1674_, 1);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_a_1674_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1680_ = v_a_1674_;
v_isShared_1681_ = v_isSharedCheck_1687_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_tail_1678_);
lean_inc(v_head_1677_);
lean_dec(v_a_1674_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1687_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; lean_object* v___x_1684_; 
v___x_1682_ = l_Lean_Level_param___override(v_head_1677_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 1, v_a_1675_);
lean_ctor_set(v___x_1680_, 0, v___x_1682_);
v___x_1684_ = v___x_1680_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1682_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_a_1675_);
v___x_1684_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
v_a_1674_ = v_tail_1678_;
v_a_1675_ = v___x_1684_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object* v_x1_1688_, lean_object* v_x2_1689_){
_start:
{
lean_object* v_fst_1690_; lean_object* v_fst_1691_; uint8_t v___x_1692_; 
v_fst_1690_ = lean_ctor_get(v_x1_1688_, 0);
v_fst_1691_ = lean_ctor_get(v_x2_1689_, 0);
v___x_1692_ = l_Lean_Name_quickLt(v_fst_1690_, v_fst_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_x1_1693_, lean_object* v_x2_1694_){
_start:
{
uint8_t v_res_1695_; lean_object* v_r_1696_; 
v_res_1695_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_x1_1693_, v_x2_1694_);
lean_dec_ref(v_x2_1694_);
lean_dec_ref(v_x1_1693_);
v_r_1696_ = lean_box(v_res_1695_);
return v_r_1696_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object* v_as_1697_, lean_object* v_k_1698_, lean_object* v_x_1699_, lean_object* v_x_1700_){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v_m_1703_; lean_object* v_a_1704_; uint8_t v___x_1705_; 
v___x_1701_ = lean_nat_add(v_x_1699_, v_x_1700_);
v___x_1702_ = lean_unsigned_to_nat(1u);
v_m_1703_ = lean_nat_shiftr(v___x_1701_, v___x_1702_);
lean_dec(v___x_1701_);
v_a_1704_ = lean_array_fget_borrowed(v_as_1697_, v_m_1703_);
v___x_1705_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_a_1704_, v_k_1698_);
if (v___x_1705_ == 0)
{
uint8_t v___x_1706_; 
lean_dec(v_x_1700_);
v___x_1706_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_k_1698_, v_a_1704_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1707_; 
lean_dec(v_m_1703_);
lean_dec(v_x_1699_);
lean_inc(v_a_1704_);
v___x_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1707_, 0, v_a_1704_);
return v___x_1707_;
}
else
{
lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1708_ = lean_unsigned_to_nat(0u);
v___x_1709_ = lean_nat_dec_eq(v_m_1703_, v___x_1708_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1710_ = lean_nat_sub(v_m_1703_, v___x_1702_);
lean_dec(v_m_1703_);
v___x_1711_ = lean_nat_dec_lt(v___x_1710_, v_x_1699_);
if (v___x_1711_ == 0)
{
v_x_1700_ = v___x_1710_;
goto _start;
}
else
{
lean_object* v___x_1713_; 
lean_dec(v___x_1710_);
lean_dec(v_x_1699_);
v___x_1713_ = lean_box(0);
return v___x_1713_;
}
}
else
{
lean_object* v___x_1714_; 
lean_dec(v_m_1703_);
lean_dec(v_x_1699_);
v___x_1714_ = lean_box(0);
return v___x_1714_;
}
}
}
else
{
lean_object* v___x_1715_; uint8_t v___x_1716_; 
lean_dec(v_x_1699_);
v___x_1715_ = lean_nat_add(v_m_1703_, v___x_1702_);
lean_dec(v_m_1703_);
v___x_1716_ = lean_nat_dec_le(v___x_1715_, v_x_1700_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; 
lean_dec(v___x_1715_);
lean_dec(v_x_1700_);
v___x_1717_ = lean_box(0);
return v___x_1717_;
}
else
{
v_x_1699_ = v___x_1715_;
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
lean_object* v___x_1728_; lean_object* v_env_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1728_ = lean_st_ref_get(v___y_1726_);
v_env_1732_ = lean_ctor_get(v___x_1728_, 0);
lean_inc_ref(v_env_1732_);
lean_dec(v___x_1728_);
v___x_1733_ = lean_box(1);
v___x_1734_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1732_, v_tac_1725_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v___x_1735_; lean_object* v_toEnvExtension_1736_; lean_object* v_asyncMode_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1735_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1736_ = lean_ctor_get(v___x_1735_, 0);
v_asyncMode_1737_ = lean_ctor_get(v_toEnvExtension_1736_, 2);
v___x_1738_ = lean_box(0);
v___x_1739_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1733_, v___x_1735_, v_env_1732_, v_asyncMode_1737_, v___x_1738_);
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
v___x_1748_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1733_, v___x_1746_, v_env_1732_, v_val_1742_, v___x_1747_);
lean_dec(v_val_1742_);
lean_dec_ref(v_env_1732_);
v___x_1749_ = lean_unsigned_to_nat(0u);
v___x_1750_ = lean_array_get_size(v___x_1748_);
v___x_1751_ = lean_nat_dec_lt(v___x_1749_, v___x_1750_);
if (v___x_1751_ == 0)
{
lean_dec_ref(v___x_1748_);
lean_del_object(v___x_1744_);
lean_dec(v_tac_1725_);
goto v___jp_1729_;
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
goto v___jp_1729_;
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
goto v___jp_1729_;
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
v___jp_1729_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1730_ = lean_box(0);
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
return v___x_1731_;
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
v___x_1820_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
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
size_t v_x_17418__boxed_1870_; lean_object* v_res_1871_; 
v_x_17418__boxed_1870_ = lean_unbox_usize(v_x_1868_);
lean_dec(v_x_1868_);
v_res_1871_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1867_, v_x_17418__boxed_1870_, v_x_1869_);
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
v___x_1878_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
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
v___x_1903_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_1904_ = l_Lean_Expr_const___override(v_n_1896_, v___y_1901_);
v___x_1905_ = lean_unsigned_to_nat(32u);
v___x_1906_ = lean_mk_empty_array_with_capacity(v___x_1905_);
lean_dec_ref(v___x_1906_);
v___x_1907_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2);
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
lean_object* v_currPos_1997_; lean_object* v_searcher_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2024_; 
v_currPos_1997_ = lean_ctor_get(v_a_1987_, 0);
v_searcher_1998_ = lean_ctor_get(v_a_1987_, 1);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_a_1987_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2000_ = v_a_1987_;
v_isShared_2001_ = v_isSharedCheck_2024_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_searcher_1998_);
lean_inc(v_currPos_1997_);
lean_dec(v_a_1987_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2024_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v_startInclusive_2002_; lean_object* v_endExclusive_2003_; lean_object* v___x_2004_; uint8_t v___x_2005_; 
v_startInclusive_2002_ = lean_ctor_get(v___x_1985_, 1);
v_endExclusive_2003_ = lean_ctor_get(v___x_1985_, 2);
v___x_2004_ = lean_nat_sub(v_endExclusive_2003_, v_startInclusive_2002_);
v___x_2005_ = lean_nat_dec_eq(v_searcher_1998_, v___x_2004_);
lean_dec(v___x_2004_);
if (v___x_2005_ == 0)
{
uint32_t v___x_2006_; uint32_t v___x_2007_; uint8_t v___x_2008_; 
v___x_2006_ = 10;
v___x_2007_ = lean_string_utf8_get_fast(v_val_1984_, v_searcher_1998_);
v___x_2008_ = lean_uint32_dec_eq(v___x_2007_, v___x_2006_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; lean_object* v___x_2011_; 
v___x_2009_ = lean_string_utf8_next_fast(v_val_1984_, v_searcher_1998_);
lean_dec(v_searcher_1998_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 1, v___x_2009_);
v___x_2011_ = v___x_2000_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_currPos_1997_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v___x_2009_);
v___x_2011_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
v_a_1987_ = v___x_2011_;
goto _start;
}
}
else
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v_slice_2017_; lean_object* v_nextIt_2019_; 
v___x_2014_ = lean_string_utf8_next_fast(v_val_1984_, v_searcher_1998_);
v___x_2015_ = lean_nat_sub(v___x_2014_, v_searcher_1998_);
v___x_2016_ = lean_nat_add(v_searcher_1998_, v___x_2015_);
lean_dec(v___x_2015_);
v_slice_2017_ = l_String_Slice_subslice_x21(v___x_1985_, v_currPos_1997_, v_searcher_1998_);
lean_inc(v___x_2016_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 1, v___x_2016_);
lean_ctor_set(v___x_2000_, 0, v___x_2016_);
v_nextIt_2019_ = v___x_2000_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2016_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___x_2016_);
v_nextIt_2019_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v_startInclusive_2020_; lean_object* v_endExclusive_2021_; 
v_startInclusive_2020_ = lean_ctor_get(v_slice_2017_, 0);
lean_inc(v_startInclusive_2020_);
v_endExclusive_2021_ = lean_ctor_get(v_slice_2017_, 1);
lean_inc(v_endExclusive_2021_);
lean_dec_ref(v_slice_2017_);
v_it_1990_ = v_nextIt_2019_;
v_startInclusive_1991_ = v_startInclusive_2020_;
v_endExclusive_1992_ = v_endExclusive_2021_;
goto v___jp_1989_;
}
}
}
else
{
lean_object* v___x_2023_; 
lean_del_object(v___x_2000_);
lean_dec(v_searcher_1998_);
v___x_2023_ = lean_box(1);
lean_inc(v___x_1986_);
v_it_1990_ = v___x_2023_;
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
v___x_1993_ = lean_string_utf8_extract(v_val_1984_, v_startInclusive_1991_, v_endExclusive_1992_);
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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object* v_val_2025_, lean_object* v___x_2026_, lean_object* v___x_2027_, lean_object* v_a_2028_, lean_object* v_b_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2025_, v___x_2026_, v___x_2027_, v_a_2028_, v_b_2029_);
lean_dec_ref(v___x_2026_);
lean_dec_ref(v_val_2025_);
return v_res_2030_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2(void){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1));
v___x_2035_ = l_Lean_stringToMessageData(v___x_2034_);
return v___x_2035_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4(void){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3));
v___x_2038_ = l_Lean_stringToMessageData(v___x_2037_);
return v___x_2038_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6(void){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2040_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5));
v___x_2041_ = l_Lean_stringToMessageData(v___x_2040_);
return v___x_2041_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9(void){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8));
v___x_2046_ = l_Lean_MessageData_ofFormat(v___x_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_x_2049_, lean_object* v_x_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
if (lean_obj_tag(v_x_2049_) == 0)
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = l_List_reverse___redArg(v_x_2050_);
v___x_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
return v___x_2055_;
}
else
{
lean_object* v_head_2056_; lean_object* v_tail_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2154_; 
v_head_2056_ = lean_ctor_get(v_x_2049_, 0);
v_tail_2057_ = lean_ctor_get(v_x_2049_, 1);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_x_2049_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2059_ = v_x_2049_;
v_isShared_2060_ = v_isSharedCheck_2154_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_tail_2057_);
lean_inc(v_head_2056_);
lean_dec(v_x_2049_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2154_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v_snd_2074_; lean_object* v_fst_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2153_; 
v_snd_2074_ = lean_ctor_get(v_head_2056_, 1);
v_fst_2075_ = lean_ctor_get(v_head_2056_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_head_2056_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2077_ = v_head_2056_;
v_isShared_2078_ = v_isSharedCheck_2153_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_snd_2074_);
lean_inc(v_fst_2075_);
lean_dec(v_head_2056_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2153_;
goto v_resetjp_2076_;
}
v___jp_2061_:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2071_; 
v___x_2066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___y_2064_);
lean_ctor_set(v___x_2066_, 1, v___y_2065_);
v___x_2067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
lean_ctor_set(v___x_2067_, 1, v___y_2062_);
v___x_2068_ = l_Lean_MessageData_nestD(v___x_2067_);
lean_inc_ref(v___y_2063_);
v___x_2069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___y_2063_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 1, v_x_2050_);
lean_ctor_set(v___x_2059_, 0, v___x_2069_);
v___x_2071_ = v___x_2059_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2069_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v_x_2050_);
v___x_2071_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
v_x_2049_ = v_tail_2057_;
v_x_2050_ = v___x_2071_;
goto _start;
}
}
v_resetjp_2076_:
{
lean_object* v_fst_2079_; lean_object* v_snd_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2152_; 
v_fst_2079_ = lean_ctor_get(v_snd_2074_, 0);
v_snd_2080_ = lean_ctor_get(v_snd_2074_, 1);
v_isSharedCheck_2152_ = !lean_is_exclusive(v_snd_2074_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2082_ = v_snd_2074_;
v_isShared_2083_ = v_isSharedCheck_2152_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_snd_2080_);
lean_inc(v_fst_2079_);
lean_dec(v_snd_2074_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2152_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v_a_2107_; lean_object* v___y_2123_; lean_object* v___x_2132_; 
v___x_2132_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2048_, v_fst_2075_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v___x_2133_; 
v___x_2133_ = l_Lean_MessageData_nil;
v_a_2107_ = v___x_2133_;
goto v___jp_2106_;
}
else
{
lean_object* v_val_2134_; 
v_val_2134_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_val_2134_);
lean_dec_ref_known(v___x_2132_, 1);
if (lean_obj_tag(v_val_2134_) == 0)
{
lean_object* v_size_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v_size_2135_ = lean_ctor_get(v_val_2134_, 0);
v___x_2136_ = lean_mk_empty_array_with_capacity(v_size_2135_);
v___x_2137_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v___x_2136_, v_val_2134_);
v___x_2138_ = lean_array_get_size(v___x_2137_);
v___x_2143_ = lean_unsigned_to_nat(0u);
v___x_2144_ = lean_nat_dec_eq(v___x_2138_, v___x_2143_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___y_2148_; uint8_t v___x_2150_; 
v___x_2145_ = lean_unsigned_to_nat(1u);
v___x_2146_ = lean_nat_sub(v___x_2138_, v___x_2145_);
v___x_2150_ = lean_nat_dec_le(v___x_2143_, v___x_2146_);
if (v___x_2150_ == 0)
{
lean_inc(v___x_2146_);
v___y_2148_ = v___x_2146_;
goto v___jp_2147_;
}
else
{
v___y_2148_ = v___x_2143_;
goto v___jp_2147_;
}
v___jp_2147_:
{
uint8_t v___x_2149_; 
v___x_2149_ = lean_nat_dec_le(v___y_2148_, v___x_2146_);
if (v___x_2149_ == 0)
{
lean_dec(v___x_2146_);
lean_inc(v___y_2148_);
v___y_2140_ = v___y_2148_;
v___y_2141_ = v___y_2148_;
goto v___jp_2139_;
}
else
{
v___y_2140_ = v___y_2148_;
v___y_2141_ = v___x_2146_;
goto v___jp_2139_;
}
}
}
else
{
v___y_2123_ = v___x_2137_;
goto v___jp_2122_;
}
v___jp_2139_:
{
lean_object* v___x_2142_; 
v___x_2142_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v___x_2138_, v___x_2137_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
v___y_2123_ = v___x_2142_;
goto v___jp_2122_;
}
}
else
{
lean_object* v___x_2151_; 
v___x_2151_ = l_Lean_MessageData_nil;
v_a_2107_ = v___x_2151_;
goto v___jp_2106_;
}
}
v___jp_2084_:
{
lean_object* v___x_2090_; 
if (v_isShared_2083_ == 0)
{
lean_ctor_set_tag(v___x_2082_, 7);
lean_ctor_set(v___x_2082_, 1, v___y_2088_);
lean_ctor_set(v___x_2082_, 0, v___y_2085_);
v___x_2090_ = v___x_2082_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___y_2085_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v___y_2088_);
v___x_2090_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
if (lean_obj_tag(v_snd_2080_) == 0)
{
lean_object* v___x_2091_; 
lean_del_object(v___x_2077_);
v___x_2091_ = l_Lean_MessageData_nil;
v___y_2062_ = v___y_2086_;
v___y_2063_ = v___y_2087_;
v___y_2064_ = v___x_2090_;
v___y_2065_ = v___x_2091_;
goto v___jp_2061_;
}
else
{
lean_object* v_val_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2103_; 
v_val_2092_ = lean_ctor_get(v_snd_2080_, 0);
lean_inc_n(v_val_2092_, 2);
lean_dec_ref_known(v_snd_2080_, 1);
v___x_2093_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2094_ = lean_unsigned_to_nat(0u);
v___x_2095_ = lean_string_utf8_byte_size(v_val_2092_);
v___x_2096_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2096_, 0, v_val_2092_);
lean_ctor_set(v___x_2096_, 1, v___x_2094_);
lean_ctor_set(v___x_2096_, 2, v___x_2095_);
v___x_2097_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v___x_2096_);
v___x_2098_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0));
v___x_2099_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2092_, v___x_2096_, v___x_2095_, v___x_2097_, v___x_2098_);
lean_dec_ref_known(v___x_2096_, 3);
lean_dec(v_val_2092_);
v___x_2100_ = lean_array_to_list(v___x_2099_);
v___x_2101_ = l_Lean_MessageData_joinSep(v___x_2100_, v___x_2093_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set_tag(v___x_2077_, 7);
lean_ctor_set(v___x_2077_, 1, v___x_2101_);
lean_ctor_set(v___x_2077_, 0, v___x_2093_);
v___x_2103_ = v___x_2077_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2093_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
v___y_2062_ = v___y_2086_;
v___y_2063_ = v___y_2087_;
v___y_2064_ = v___x_2090_;
v___y_2065_ = v___x_2103_;
goto v___jp_2061_;
}
}
}
}
v___jp_2106_:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; lean_object* v___x_2114_; uint8_t v___x_2115_; 
v___x_2108_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2);
v___x_2109_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
lean_inc(v_fst_2075_);
v___x_2110_ = l_Lean_MessageData_ofName(v_fst_2075_);
v___x_2111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2109_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
v___x_2112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
lean_ctor_set(v___x_2112_, 1, v___x_2109_);
v___x_2113_ = 1;
v___x_2114_ = l_Lean_Name_toString(v_fst_2075_, v___x_2113_);
v___x_2115_ = lean_string_dec_eq(v___x_2114_, v_fst_2079_);
lean_dec_ref(v___x_2114_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2116_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4);
v___x_2117_ = l_Lean_stringToMessageData(v_fst_2079_);
v___x_2118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2116_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___x_2119_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6);
v___x_2120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2118_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
v___y_2085_ = v___x_2112_;
v___y_2086_ = v_a_2107_;
v___y_2087_ = v___x_2108_;
v___y_2088_ = v___x_2120_;
goto v___jp_2084_;
}
else
{
lean_object* v___x_2121_; 
lean_dec(v_fst_2079_);
v___x_2121_ = l_Lean_MessageData_nil;
v___y_2085_ = v___x_2112_;
v___y_2086_ = v_a_2107_;
v___y_2087_ = v___x_2108_;
v___y_2088_ = v___x_2121_;
goto v___jp_2084_;
}
}
v___jp_2122_:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2124_ = lean_array_to_list(v___y_2123_);
v___x_2125_ = lean_box(0);
v___x_2126_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_2047_, v___x_2124_, v___x_2125_, v___y_2051_, v___y_2052_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v___x_2128_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2129_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9);
v___x_2130_ = l_Lean_MessageData_joinSep(v_a_2127_, v___x_2129_);
v___x_2131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2128_);
lean_ctor_set(v___x_2131_, 1, v___x_2130_);
v_a_2107_ = v___x_2131_;
goto v___jp_2106_;
}
else
{
lean_del_object(v___x_2082_);
lean_dec(v_snd_2080_);
lean_dec(v_fst_2079_);
lean_del_object(v___x_2077_);
lean_dec(v_fst_2075_);
lean_del_object(v___x_2059_);
lean_dec(v_tail_2057_);
lean_dec(v_x_2050_);
return v___x_2126_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_x_2157_, lean_object* v_x_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_2155_, v_a_2156_, v_x_2157_, v_x_2158_, v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v_a_2156_);
lean_dec(v_a_2155_);
return v_res_2162_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(uint8_t v___y_2164_, uint8_t v_suppressElabErrors_2165_, lean_object* v_x_2166_){
_start:
{
if (lean_obj_tag(v_x_2166_) == 1)
{
lean_object* v_pre_2167_; 
v_pre_2167_ = lean_ctor_get(v_x_2166_, 0);
if (lean_obj_tag(v_pre_2167_) == 0)
{
lean_object* v_str_2168_; lean_object* v___x_2169_; uint8_t v___x_2170_; 
v_str_2168_ = lean_ctor_get(v_x_2166_, 1);
v___x_2169_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0));
v___x_2170_ = lean_string_dec_eq(v_str_2168_, v___x_2169_);
if (v___x_2170_ == 0)
{
return v___y_2164_;
}
else
{
return v_suppressElabErrors_2165_;
}
}
else
{
return v___y_2164_;
}
}
else
{
return v___y_2164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed(lean_object* v___y_2171_, lean_object* v_suppressElabErrors_2172_, lean_object* v_x_2173_){
_start:
{
uint8_t v___y_18038__boxed_2174_; uint8_t v_suppressElabErrors_boxed_2175_; uint8_t v_res_2176_; lean_object* v_r_2177_; 
v___y_18038__boxed_2174_ = lean_unbox(v___y_2171_);
v_suppressElabErrors_boxed_2175_ = lean_unbox(v_suppressElabErrors_2172_);
v_res_2176_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(v___y_18038__boxed_2174_, v_suppressElabErrors_boxed_2175_, v_x_2173_);
lean_dec(v_x_2173_);
v_r_2177_ = lean_box(v_res_2176_);
return v_r_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(lean_object* v_ref_2178_, lean_object* v_msgData_2179_, uint8_t v_severity_2180_, uint8_t v_isSilent_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
uint8_t v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; uint8_t v___y_2192_; lean_object* v___y_2193_; uint8_t v___y_2250_; lean_object* v___y_2251_; uint8_t v___y_2252_; uint8_t v___y_2253_; lean_object* v___y_2254_; uint8_t v___y_2278_; uint8_t v___y_2279_; lean_object* v___y_2280_; uint8_t v___y_2281_; lean_object* v___y_2282_; uint8_t v___y_2286_; uint8_t v___y_2287_; uint8_t v___y_2288_; uint8_t v___x_2303_; uint8_t v___y_2305_; uint8_t v___y_2306_; uint8_t v___y_2307_; uint8_t v___y_2309_; uint8_t v___x_2321_; 
v___x_2303_ = 2;
v___x_2321_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2180_, v___x_2303_);
if (v___x_2321_ == 0)
{
v___y_2309_ = v___x_2321_;
goto v___jp_2308_;
}
else
{
uint8_t v___x_2322_; 
lean_inc_ref(v_msgData_2179_);
v___x_2322_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2179_);
v___y_2309_ = v___x_2322_;
goto v___jp_2308_;
}
v___jp_2185_:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_Elab_Command_getScope___redArg(v___y_2193_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2196_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2194_, 1);
v___x_2196_ = l_Lean_Elab_Command_getScope___redArg(v___y_2193_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2232_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2199_ = v___x_2196_;
v_isShared_2200_ = v_isSharedCheck_2232_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2196_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2232_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2201_; lean_object* v_currNamespace_2202_; lean_object* v_openDecls_2203_; lean_object* v_env_2204_; lean_object* v_messages_2205_; lean_object* v_scopes_2206_; lean_object* v_usedQuotCtxts_2207_; lean_object* v_nextMacroScope_2208_; lean_object* v_maxRecDepth_2209_; lean_object* v_ngen_2210_; lean_object* v_auxDeclNGen_2211_; lean_object* v_infoState_2212_; lean_object* v_traceState_2213_; lean_object* v_snapshotTasks_2214_; lean_object* v_prevLinterStates_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2231_; 
v___x_2201_ = lean_st_ref_take(v___y_2193_);
v_currNamespace_2202_ = lean_ctor_get(v_a_2195_, 2);
lean_inc(v_currNamespace_2202_);
lean_dec(v_a_2195_);
v_openDecls_2203_ = lean_ctor_get(v_a_2197_, 3);
lean_inc(v_openDecls_2203_);
lean_dec(v_a_2197_);
v_env_2204_ = lean_ctor_get(v___x_2201_, 0);
v_messages_2205_ = lean_ctor_get(v___x_2201_, 1);
v_scopes_2206_ = lean_ctor_get(v___x_2201_, 2);
v_usedQuotCtxts_2207_ = lean_ctor_get(v___x_2201_, 3);
v_nextMacroScope_2208_ = lean_ctor_get(v___x_2201_, 4);
v_maxRecDepth_2209_ = lean_ctor_get(v___x_2201_, 5);
v_ngen_2210_ = lean_ctor_get(v___x_2201_, 6);
v_auxDeclNGen_2211_ = lean_ctor_get(v___x_2201_, 7);
v_infoState_2212_ = lean_ctor_get(v___x_2201_, 8);
v_traceState_2213_ = lean_ctor_get(v___x_2201_, 9);
v_snapshotTasks_2214_ = lean_ctor_get(v___x_2201_, 10);
v_prevLinterStates_2215_ = lean_ctor_get(v___x_2201_, 11);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2217_ = v___x_2201_;
v_isShared_2218_ = v_isSharedCheck_2231_;
goto v_resetjp_2216_;
}
else
{
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
lean_dec(v___x_2201_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2231_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2219_, 0, v_currNamespace_2202_);
lean_ctor_set(v___x_2219_, 1, v_openDecls_2203_);
v___x_2220_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
lean_ctor_set(v___x_2220_, 1, v___y_2189_);
lean_inc_ref(v___y_2187_);
lean_inc_ref(v___y_2190_);
v___x_2221_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2221_, 0, v___y_2190_);
lean_ctor_set(v___x_2221_, 1, v___y_2188_);
lean_ctor_set(v___x_2221_, 2, v___y_2191_);
lean_ctor_set(v___x_2221_, 3, v___y_2187_);
lean_ctor_set(v___x_2221_, 4, v___x_2220_);
lean_ctor_set_uint8(v___x_2221_, sizeof(void*)*5, v___y_2192_);
lean_ctor_set_uint8(v___x_2221_, sizeof(void*)*5 + 1, v___y_2186_);
lean_ctor_set_uint8(v___x_2221_, sizeof(void*)*5 + 2, v_isSilent_2181_);
v___x_2222_ = l_Lean_MessageLog_add(v___x_2221_, v_messages_2205_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 1, v___x_2222_);
v___x_2224_ = v___x_2217_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_env_2204_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v___x_2222_);
lean_ctor_set(v_reuseFailAlloc_2230_, 2, v_scopes_2206_);
lean_ctor_set(v_reuseFailAlloc_2230_, 3, v_usedQuotCtxts_2207_);
lean_ctor_set(v_reuseFailAlloc_2230_, 4, v_nextMacroScope_2208_);
lean_ctor_set(v_reuseFailAlloc_2230_, 5, v_maxRecDepth_2209_);
lean_ctor_set(v_reuseFailAlloc_2230_, 6, v_ngen_2210_);
lean_ctor_set(v_reuseFailAlloc_2230_, 7, v_auxDeclNGen_2211_);
lean_ctor_set(v_reuseFailAlloc_2230_, 8, v_infoState_2212_);
lean_ctor_set(v_reuseFailAlloc_2230_, 9, v_traceState_2213_);
lean_ctor_set(v_reuseFailAlloc_2230_, 10, v_snapshotTasks_2214_);
lean_ctor_set(v_reuseFailAlloc_2230_, 11, v_prevLinterStates_2215_);
v___x_2224_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2228_; 
v___x_2225_ = lean_st_ref_set(v___y_2193_, v___x_2224_);
v___x_2226_ = lean_box(0);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v___x_2226_);
v___x_2228_ = v___x_2199_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec(v_a_2195_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2189_);
lean_dec_ref(v___y_2188_);
v_a_2233_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2196_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2196_);
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
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2189_);
lean_dec_ref(v___y_2188_);
v_a_2241_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2194_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2194_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
v___jp_2249_:
{
lean_object* v_fileName_2255_; lean_object* v_fileMap_2256_; uint8_t v_suppressElabErrors_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2276_; 
v_fileName_2255_ = lean_ctor_get(v___y_2182_, 0);
v_fileMap_2256_ = lean_ctor_get(v___y_2182_, 1);
v_suppressElabErrors_2257_ = lean_ctor_get_uint8(v___y_2182_, sizeof(void*)*10);
v___x_2258_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2179_);
v___x_2259_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v___x_2258_, v___y_2183_);
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2262_ = v___x_2259_;
v_isShared_2263_ = v_isSharedCheck_2276_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2259_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2276_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
lean_inc_ref_n(v_fileMap_2256_, 2);
v___x_2264_ = l_Lean_FileMap_toPosition(v_fileMap_2256_, v___y_2251_);
lean_dec(v___y_2251_);
v___x_2265_ = l_Lean_FileMap_toPosition(v_fileMap_2256_, v___y_2254_);
lean_dec(v___y_2254_);
v___x_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
v___x_2267_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
if (v_suppressElabErrors_2257_ == 0)
{
lean_del_object(v___x_2262_);
v___y_2186_ = v___y_2252_;
v___y_2187_ = v___x_2267_;
v___y_2188_ = v___x_2264_;
v___y_2189_ = v_a_2260_;
v___y_2190_ = v_fileName_2255_;
v___y_2191_ = v___x_2266_;
v___y_2192_ = v___y_2253_;
v___y_2193_ = v___y_2183_;
goto v___jp_2185_;
}
else
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___f_2270_; uint8_t v___x_2271_; 
v___x_2268_ = lean_box(v___y_2250_);
v___x_2269_ = lean_box(v_suppressElabErrors_2257_);
v___f_2270_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2270_, 0, v___x_2268_);
lean_closure_set(v___f_2270_, 1, v___x_2269_);
lean_inc(v_a_2260_);
v___x_2271_ = l_Lean_MessageData_hasTag(v___f_2270_, v_a_2260_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; lean_object* v___x_2274_; 
lean_dec_ref_known(v___x_2266_, 1);
lean_dec_ref(v___x_2264_);
lean_dec(v_a_2260_);
v___x_2272_ = lean_box(0);
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 0, v___x_2272_);
v___x_2274_ = v___x_2262_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
else
{
lean_del_object(v___x_2262_);
v___y_2186_ = v___y_2252_;
v___y_2187_ = v___x_2267_;
v___y_2188_ = v___x_2264_;
v___y_2189_ = v_a_2260_;
v___y_2190_ = v_fileName_2255_;
v___y_2191_ = v___x_2266_;
v___y_2192_ = v___y_2253_;
v___y_2193_ = v___y_2183_;
goto v___jp_2185_;
}
}
}
}
v___jp_2277_:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lean_Syntax_getTailPos_x3f(v___y_2280_, v___y_2281_);
lean_dec(v___y_2280_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_inc(v___y_2282_);
v___y_2250_ = v___y_2278_;
v___y_2251_ = v___y_2282_;
v___y_2252_ = v___y_2279_;
v___y_2253_ = v___y_2281_;
v___y_2254_ = v___y_2282_;
goto v___jp_2249_;
}
else
{
lean_object* v_val_2284_; 
v_val_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_val_2284_);
lean_dec_ref_known(v___x_2283_, 1);
v___y_2250_ = v___y_2278_;
v___y_2251_ = v___y_2282_;
v___y_2252_ = v___y_2279_;
v___y_2253_ = v___y_2281_;
v___y_2254_ = v_val_2284_;
goto v___jp_2249_;
}
}
v___jp_2285_:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Lean_Elab_Command_getRef___redArg(v___y_2182_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; lean_object* v_ref_2291_; lean_object* v___x_2292_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2290_);
lean_dec_ref_known(v___x_2289_, 1);
v_ref_2291_ = l_Lean_replaceRef(v_ref_2178_, v_a_2290_);
lean_dec(v_a_2290_);
v___x_2292_ = l_Lean_Syntax_getPos_x3f(v_ref_2291_, v___y_2287_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v___x_2293_; 
v___x_2293_ = lean_unsigned_to_nat(0u);
v___y_2278_ = v___y_2286_;
v___y_2279_ = v___y_2288_;
v___y_2280_ = v_ref_2291_;
v___y_2281_ = v___y_2287_;
v___y_2282_ = v___x_2293_;
goto v___jp_2277_;
}
else
{
lean_object* v_val_2294_; 
v_val_2294_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_val_2294_);
lean_dec_ref_known(v___x_2292_, 1);
v___y_2278_ = v___y_2286_;
v___y_2279_ = v___y_2288_;
v___y_2280_ = v_ref_2291_;
v___y_2281_ = v___y_2287_;
v___y_2282_ = v_val_2294_;
goto v___jp_2277_;
}
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
lean_dec_ref(v_msgData_2179_);
v_a_2295_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2289_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2289_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
v___jp_2304_:
{
if (v___y_2307_ == 0)
{
v___y_2286_ = v___y_2305_;
v___y_2287_ = v___y_2306_;
v___y_2288_ = v_severity_2180_;
goto v___jp_2285_;
}
else
{
v___y_2286_ = v___y_2305_;
v___y_2287_ = v___y_2306_;
v___y_2288_ = v___x_2303_;
goto v___jp_2285_;
}
}
v___jp_2308_:
{
if (v___y_2309_ == 0)
{
lean_object* v___x_2310_; lean_object* v_scopes_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v_opts_2314_; uint8_t v___x_2315_; uint8_t v___x_2316_; 
v___x_2310_ = lean_st_ref_get(v___y_2183_);
v_scopes_2311_ = lean_ctor_get(v___x_2310_, 2);
lean_inc(v_scopes_2311_);
lean_dec(v___x_2310_);
v___x_2312_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2313_ = l_List_head_x21___redArg(v___x_2312_, v_scopes_2311_);
lean_dec(v_scopes_2311_);
v_opts_2314_ = lean_ctor_get(v___x_2313_, 1);
lean_inc_ref(v_opts_2314_);
lean_dec(v___x_2313_);
v___x_2315_ = 1;
v___x_2316_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2180_, v___x_2315_);
if (v___x_2316_ == 0)
{
lean_dec_ref(v_opts_2314_);
v___y_2305_ = v___y_2309_;
v___y_2306_ = v___y_2309_;
v___y_2307_ = v___x_2316_;
goto v___jp_2304_;
}
else
{
lean_object* v___x_2317_; uint8_t v___x_2318_; 
v___x_2317_ = l_Lean_warningAsError;
v___x_2318_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_2314_, v___x_2317_);
lean_dec_ref(v_opts_2314_);
v___y_2305_ = v___y_2309_;
v___y_2306_ = v___y_2309_;
v___y_2307_ = v___x_2318_;
goto v___jp_2304_;
}
}
else
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
lean_dec_ref(v_msgData_2179_);
v___x_2319_ = lean_box(0);
v___x_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
return v___x_2320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___boxed(lean_object* v_ref_2323_, lean_object* v_msgData_2324_, lean_object* v_severity_2325_, lean_object* v_isSilent_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
uint8_t v_severity_boxed_2330_; uint8_t v_isSilent_boxed_2331_; lean_object* v_res_2332_; 
v_severity_boxed_2330_ = lean_unbox(v_severity_2325_);
v_isSilent_boxed_2331_ = lean_unbox(v_isSilent_2326_);
v_res_2332_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_ref_2323_, v_msgData_2324_, v_severity_boxed_2330_, v_isSilent_boxed_2331_, v___y_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v_ref_2323_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(lean_object* v_msgData_2333_, uint8_t v_severity_2334_, uint8_t v_isSilent_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_Elab_Command_getRef___redArg(v___y_2336_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2341_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref_known(v___x_2339_, 1);
v___x_2341_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_a_2340_, v_msgData_2333_, v_severity_2334_, v_isSilent_2335_, v___y_2336_, v___y_2337_);
lean_dec(v_a_2340_);
return v___x_2341_;
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec_ref(v_msgData_2333_);
v_a_2342_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2339_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2339_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26___boxed(lean_object* v_msgData_2350_, lean_object* v_severity_2351_, lean_object* v_isSilent_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
uint8_t v_severity_boxed_2356_; uint8_t v_isSilent_boxed_2357_; lean_object* v_res_2358_; 
v_severity_boxed_2356_ = lean_unbox(v_severity_2351_);
v_isSilent_boxed_2357_ = lean_unbox(v_isSilent_2352_);
v_res_2358_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_2350_, v_severity_boxed_2356_, v_isSilent_boxed_2357_, v___y_2353_, v___y_2354_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object* v_msgData_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
uint8_t v___x_2363_; uint8_t v___x_2364_; lean_object* v___x_2365_; 
v___x_2363_ = 0;
v___x_2364_ = 0;
v___x_2365_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_2359_, v___x_2363_, v___x_2364_, v___y_2360_, v___y_2361_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object* v_msgData_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v_msgData_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object* v_init_2371_, lean_object* v_x_2372_){
_start:
{
if (lean_obj_tag(v_x_2372_) == 0)
{
lean_object* v_k_2374_; lean_object* v_v_2375_; lean_object* v_l_2376_; lean_object* v_r_2377_; lean_object* v___x_2378_; lean_object* v_a_2379_; lean_object* v_a_2380_; lean_object* v___x_2381_; 
v_k_2374_ = lean_ctor_get(v_x_2372_, 1);
lean_inc(v_k_2374_);
v_v_2375_ = lean_ctor_get(v_x_2372_, 2);
lean_inc(v_v_2375_);
v_l_2376_ = lean_ctor_get(v_x_2372_, 3);
lean_inc(v_l_2376_);
v_r_2377_ = lean_ctor_get(v_x_2372_, 4);
lean_inc(v_r_2377_);
lean_dec_ref_known(v_x_2372_, 5);
v___x_2378_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_2371_, v_l_2376_);
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref(v___x_2378_);
v_a_2380_ = lean_ctor_get(v_a_2379_, 0);
lean_inc(v_a_2380_);
lean_dec(v_a_2379_);
v___x_2381_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2374_, v_v_2375_, v_a_2380_);
v_init_2371_ = v___x_2381_;
v_x_2372_ = v_r_2377_;
goto _start;
}
else
{
lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2383_, 0, v_init_2371_);
v___x_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2383_);
return v___x_2384_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object* v_init_2385_, lean_object* v_x_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_2385_, v_x_2386_);
return v_res_2388_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(uint8_t v___x_2389_, lean_object* v_x1_2390_, lean_object* v_x2_2391_){
_start:
{
lean_object* v_fst_2392_; lean_object* v_fst_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; uint8_t v___x_2396_; 
v_fst_2392_ = lean_ctor_get(v_x1_2390_, 0);
lean_inc(v_fst_2392_);
lean_dec_ref(v_x1_2390_);
v_fst_2393_ = lean_ctor_get(v_x2_2391_, 0);
lean_inc(v_fst_2393_);
lean_dec_ref(v_x2_2391_);
v___x_2394_ = l_Lean_Name_toString(v_fst_2392_, v___x_2389_);
v___x_2395_ = l_Lean_Name_toString(v_fst_2393_, v___x_2389_);
v___x_2396_ = lean_string_dec_lt(v___x_2394_, v___x_2395_);
lean_dec_ref(v___x_2395_);
lean_dec_ref(v___x_2394_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0___boxed(lean_object* v___x_2397_, lean_object* v_x1_2398_, lean_object* v_x2_2399_){
_start:
{
uint8_t v___x_18381__boxed_2400_; uint8_t v_res_2401_; lean_object* v_r_2402_; 
v___x_18381__boxed_2400_ = lean_unbox(v___x_2397_);
v_res_2401_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_18381__boxed_2400_, v_x1_2398_, v_x2_2399_);
v_r_2402_ = lean_box(v_res_2401_);
return v_r_2402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(lean_object* v_hi_2403_, lean_object* v_pivot_2404_, lean_object* v_as_2405_, lean_object* v_i_2406_, lean_object* v_k_2407_){
_start:
{
uint8_t v___x_2408_; 
v___x_2408_ = lean_nat_dec_lt(v_k_2407_, v_hi_2403_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
lean_dec(v_k_2407_);
lean_dec_ref(v_pivot_2404_);
v___x_2409_ = lean_array_fswap(v_as_2405_, v_i_2406_, v_hi_2403_);
v___x_2410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2410_, 0, v_i_2406_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
return v___x_2410_;
}
else
{
lean_object* v___x_2411_; lean_object* v_fst_2412_; lean_object* v_fst_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; uint8_t v___x_2416_; 
v___x_2411_ = lean_array_fget_borrowed(v_as_2405_, v_k_2407_);
v_fst_2412_ = lean_ctor_get(v___x_2411_, 0);
v_fst_2413_ = lean_ctor_get(v_pivot_2404_, 0);
lean_inc(v_fst_2412_);
v___x_2414_ = l_Lean_Name_toString(v_fst_2412_, v___x_2408_);
lean_inc(v_fst_2413_);
v___x_2415_ = l_Lean_Name_toString(v_fst_2413_, v___x_2408_);
v___x_2416_ = lean_string_dec_lt(v___x_2414_, v___x_2415_);
lean_dec_ref(v___x_2415_);
lean_dec_ref(v___x_2414_);
if (v___x_2416_ == 0)
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = lean_unsigned_to_nat(1u);
v___x_2418_ = lean_nat_add(v_k_2407_, v___x_2417_);
lean_dec(v_k_2407_);
v_k_2407_ = v___x_2418_;
goto _start;
}
else
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2420_ = lean_array_fswap(v_as_2405_, v_i_2406_, v_k_2407_);
v___x_2421_ = lean_unsigned_to_nat(1u);
v___x_2422_ = lean_nat_add(v_i_2406_, v___x_2421_);
lean_dec(v_i_2406_);
v___x_2423_ = lean_nat_add(v_k_2407_, v___x_2421_);
lean_dec(v_k_2407_);
v_as_2405_ = v___x_2420_;
v_i_2406_ = v___x_2422_;
v_k_2407_ = v___x_2423_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg___boxed(lean_object* v_hi_2425_, lean_object* v_pivot_2426_, lean_object* v_as_2427_, lean_object* v_i_2428_, lean_object* v_k_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_2425_, v_pivot_2426_, v_as_2427_, v_i_2428_, v_k_2429_);
lean_dec(v_hi_2425_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(lean_object* v_n_2431_, lean_object* v_as_2432_, lean_object* v_lo_2433_, lean_object* v_hi_2434_){
_start:
{
lean_object* v___y_2436_; uint8_t v___x_2446_; 
v___x_2446_ = lean_nat_dec_lt(v_lo_2433_, v_hi_2434_);
if (v___x_2446_ == 0)
{
lean_dec(v_lo_2433_);
return v_as_2432_;
}
else
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v_mid_2449_; lean_object* v___y_2451_; lean_object* v___y_2457_; lean_object* v___x_2462_; lean_object* v___x_2463_; uint8_t v___x_2464_; 
v___x_2447_ = lean_nat_add(v_lo_2433_, v_hi_2434_);
v___x_2448_ = lean_unsigned_to_nat(1u);
v_mid_2449_ = lean_nat_shiftr(v___x_2447_, v___x_2448_);
lean_dec(v___x_2447_);
v___x_2462_ = lean_array_fget_borrowed(v_as_2432_, v_mid_2449_);
v___x_2463_ = lean_array_fget_borrowed(v_as_2432_, v_lo_2433_);
lean_inc(v___x_2463_);
lean_inc(v___x_2462_);
v___x_2464_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2446_, v___x_2462_, v___x_2463_);
if (v___x_2464_ == 0)
{
v___y_2457_ = v_as_2432_;
goto v___jp_2456_;
}
else
{
lean_object* v___x_2465_; 
v___x_2465_ = lean_array_fswap(v_as_2432_, v_lo_2433_, v_mid_2449_);
v___y_2457_ = v___x_2465_;
goto v___jp_2456_;
}
v___jp_2450_:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; uint8_t v___x_2454_; 
v___x_2452_ = lean_array_fget_borrowed(v___y_2451_, v_mid_2449_);
v___x_2453_ = lean_array_fget_borrowed(v___y_2451_, v_hi_2434_);
lean_inc(v___x_2453_);
lean_inc(v___x_2452_);
v___x_2454_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2446_, v___x_2452_, v___x_2453_);
if (v___x_2454_ == 0)
{
lean_dec(v_mid_2449_);
v___y_2436_ = v___y_2451_;
goto v___jp_2435_;
}
else
{
lean_object* v___x_2455_; 
v___x_2455_ = lean_array_fswap(v___y_2451_, v_mid_2449_, v_hi_2434_);
lean_dec(v_mid_2449_);
v___y_2436_ = v___x_2455_;
goto v___jp_2435_;
}
}
v___jp_2456_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; 
v___x_2458_ = lean_array_fget_borrowed(v___y_2457_, v_hi_2434_);
v___x_2459_ = lean_array_fget_borrowed(v___y_2457_, v_lo_2433_);
lean_inc(v___x_2459_);
lean_inc(v___x_2458_);
v___x_2460_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2446_, v___x_2458_, v___x_2459_);
if (v___x_2460_ == 0)
{
v___y_2451_ = v___y_2457_;
goto v___jp_2450_;
}
else
{
lean_object* v___x_2461_; 
v___x_2461_ = lean_array_fswap(v___y_2457_, v_lo_2433_, v_hi_2434_);
v___y_2451_ = v___x_2461_;
goto v___jp_2450_;
}
}
}
v___jp_2435_:
{
lean_object* v_pivot_2437_; lean_object* v___x_2438_; lean_object* v_fst_2439_; lean_object* v_snd_2440_; uint8_t v___x_2441_; 
v_pivot_2437_ = lean_array_fget(v___y_2436_, v_hi_2434_);
lean_inc_n(v_lo_2433_, 2);
v___x_2438_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_2434_, v_pivot_2437_, v___y_2436_, v_lo_2433_, v_lo_2433_);
v_fst_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_fst_2439_);
v_snd_2440_ = lean_ctor_get(v___x_2438_, 1);
lean_inc(v_snd_2440_);
lean_dec_ref(v___x_2438_);
v___x_2441_ = lean_nat_dec_le(v_hi_2434_, v_fst_2439_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2442_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_2431_, v_snd_2440_, v_lo_2433_, v_fst_2439_);
v___x_2443_ = lean_unsigned_to_nat(1u);
v___x_2444_ = lean_nat_add(v_fst_2439_, v___x_2443_);
lean_dec(v_fst_2439_);
v_as_2432_ = v___x_2442_;
v_lo_2433_ = v___x_2444_;
goto _start;
}
else
{
lean_dec(v_fst_2439_);
lean_dec(v_lo_2433_);
return v_snd_2440_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___boxed(lean_object* v_n_2466_, lean_object* v_as_2467_, lean_object* v_lo_2468_, lean_object* v_hi_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_2466_, v_as_2467_, v_lo_2468_, v_hi_2469_);
lean_dec(v_hi_2469_);
lean_dec(v_n_2466_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(lean_object* v_init_2471_, lean_object* v_x_2472_){
_start:
{
if (lean_obj_tag(v_x_2472_) == 0)
{
lean_object* v_k_2473_; lean_object* v_v_2474_; lean_object* v_l_2475_; lean_object* v_r_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v_k_2473_ = lean_ctor_get(v_x_2472_, 1);
v_v_2474_ = lean_ctor_get(v_x_2472_, 2);
v_l_2475_ = lean_ctor_get(v_x_2472_, 3);
v_r_2476_ = lean_ctor_get(v_x_2472_, 4);
v___x_2477_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_2471_, v_l_2475_);
lean_inc(v_v_2474_);
lean_inc(v_k_2473_);
v___x_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2478_, 0, v_k_2473_);
lean_ctor_set(v___x_2478_, 1, v_v_2474_);
v___x_2479_ = lean_array_push(v___x_2477_, v___x_2478_);
v_init_2471_ = v___x_2479_;
v_x_2472_ = v_r_2476_;
goto _start;
}
else
{
return v_init_2471_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25___boxed(lean_object* v_init_2481_, lean_object* v_x_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_2481_, v_x_2482_);
lean_dec(v_x_2482_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(lean_object* v_as_2484_, size_t v_sz_2485_, size_t v_i_2486_, lean_object* v_b_2487_){
_start:
{
uint8_t v___x_2489_; 
v___x_2489_ = lean_usize_dec_lt(v_i_2486_, v_sz_2485_);
if (v___x_2489_ == 0)
{
lean_object* v___x_2490_; 
v___x_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2490_, 0, v_b_2487_);
return v___x_2490_;
}
else
{
lean_object* v_a_2491_; lean_object* v_fst_2492_; lean_object* v_snd_2493_; lean_object* v_found_2494_; size_t v___x_2495_; size_t v___x_2496_; 
v_a_2491_ = lean_array_uget_borrowed(v_as_2484_, v_i_2486_);
v_fst_2492_ = lean_ctor_get(v_a_2491_, 0);
v_snd_2493_ = lean_ctor_get(v_a_2491_, 1);
lean_inc(v_snd_2493_);
lean_inc(v_fst_2492_);
v_found_2494_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2492_, v_snd_2493_, v_b_2487_);
v___x_2495_ = ((size_t)1ULL);
v___x_2496_ = lean_usize_add(v_i_2486_, v___x_2495_);
v_i_2486_ = v___x_2496_;
v_b_2487_ = v_found_2494_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg___boxed(lean_object* v_as_2498_, lean_object* v_sz_2499_, lean_object* v_i_2500_, lean_object* v_b_2501_, lean_object* v___y_2502_){
_start:
{
size_t v_sz_boxed_2503_; size_t v_i_boxed_2504_; lean_object* v_res_2505_; 
v_sz_boxed_2503_ = lean_unbox_usize(v_sz_2499_);
lean_dec(v_sz_2499_);
v_i_boxed_2504_ = lean_unbox_usize(v_i_2500_);
lean_dec(v_i_2500_);
v_res_2505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_2498_, v_sz_boxed_2503_, v_i_boxed_2504_, v_b_2501_);
lean_dec_ref(v_as_2498_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object* v_as_2506_, size_t v_sz_2507_, size_t v_i_2508_, lean_object* v_b_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
uint8_t v___x_2513_; 
v___x_2513_ = lean_usize_dec_lt(v_i_2508_, v_sz_2507_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2514_; 
v___x_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2514_, 0, v_b_2509_);
return v___x_2514_;
}
else
{
lean_object* v_a_2515_; size_t v_sz_2516_; size_t v___x_2517_; lean_object* v___x_2518_; 
v_a_2515_ = lean_array_uget_borrowed(v_as_2506_, v_i_2508_);
v_sz_2516_ = lean_array_size(v_a_2515_);
v___x_2517_ = ((size_t)0ULL);
v___x_2518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_a_2515_, v_sz_2516_, v___x_2517_, v_b_2509_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; size_t v___x_2520_; size_t v___x_2521_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_a_2519_);
lean_dec_ref_known(v___x_2518_, 1);
v___x_2520_ = ((size_t)1ULL);
v___x_2521_ = lean_usize_add(v_i_2508_, v___x_2520_);
v_i_2508_ = v___x_2521_;
v_b_2509_ = v_a_2519_;
goto _start;
}
else
{
return v___x_2518_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object* v_as_2523_, lean_object* v_sz_2524_, lean_object* v_i_2525_, lean_object* v_b_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
size_t v_sz_boxed_2530_; size_t v_i_boxed_2531_; lean_object* v_res_2532_; 
v_sz_boxed_2530_ = lean_unbox_usize(v_sz_2524_);
lean_dec(v_sz_2524_);
v_i_boxed_2531_ = lean_unbox_usize(v_i_2525_);
lean_dec(v_i_2525_);
v_res_2532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_as_2523_, v_sz_boxed_2530_, v_i_boxed_2531_, v_b_2526_, v___y_2527_, v___y_2528_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec_ref(v_as_2523_);
return v_res_2532_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2533_ = lean_box(1);
v___x_2534_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2533_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v___y_2541_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___x_2556_; lean_object* v_env_2557_; lean_object* v___x_2558_; lean_object* v_toEnvExtension_2559_; lean_object* v_asyncMode_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v_a_2566_; lean_object* v_a_2568_; lean_object* v_a_2591_; 
v___x_2556_ = lean_st_ref_get(v___y_2538_);
v_env_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc_ref_n(v_env_2557_, 2);
lean_dec(v___x_2556_);
v___x_2558_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2559_ = lean_ctor_get(v___x_2558_, 0);
v_asyncMode_2560_ = lean_ctor_get(v_toEnvExtension_2559_, 2);
v___x_2561_ = lean_box(1);
v___x_2562_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0, &l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0);
v___x_2563_ = lean_box(0);
v___x_2564_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2561_, v___x_2558_, v_env_2557_, v_asyncMode_2560_, v___x_2563_);
v___x_2565_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v___x_2561_, v___x_2564_);
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref(v___x_2565_);
v_a_2591_ = lean_ctor_get(v_a_2566_, 0);
lean_inc(v_a_2591_);
lean_dec(v_a_2566_);
v_a_2568_ = v_a_2591_;
goto v___jp_2567_;
v___jp_2540_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = lean_array_to_list(v___y_2541_);
v___x_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
return v___x_2543_;
}
v___jp_2544_:
{
lean_object* v___x_2549_; 
v___x_2549_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v___y_2545_, v___y_2547_, v___y_2546_, v___y_2548_);
lean_dec(v___y_2548_);
lean_dec(v___y_2545_);
v___y_2541_ = v___x_2549_;
goto v___jp_2540_;
}
v___jp_2550_:
{
uint8_t v___x_2555_; 
v___x_2555_ = lean_nat_dec_le(v___y_2554_, v___y_2552_);
if (v___x_2555_ == 0)
{
lean_dec(v___y_2552_);
lean_inc(v___y_2554_);
v___y_2545_ = v___y_2551_;
v___y_2546_ = v___y_2554_;
v___y_2547_ = v___y_2553_;
v___y_2548_ = v___y_2554_;
goto v___jp_2544_;
}
else
{
v___y_2545_ = v___y_2551_;
v___y_2546_ = v___y_2554_;
v___y_2547_ = v___y_2553_;
v___y_2548_ = v___y_2552_;
goto v___jp_2544_;
}
}
v___jp_2567_:
{
lean_object* v___x_2569_; lean_object* v_importedEntries_2570_; size_t v_sz_2571_; size_t v___x_2572_; lean_object* v___x_2573_; 
v___x_2569_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2562_, v_toEnvExtension_2559_, v_env_2557_, v_asyncMode_2560_, v___x_2563_);
v_importedEntries_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc_ref(v_importedEntries_2570_);
lean_dec(v___x_2569_);
v_sz_2571_ = lean_array_size(v_importedEntries_2570_);
v___x_2572_ = ((size_t)0ULL);
v___x_2573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_importedEntries_2570_, v_sz_2571_, v___x_2572_, v_a_2568_, v___y_2537_, v___y_2538_);
lean_dec_ref(v_importedEntries_2570_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v_arr_2577_; lean_object* v___x_2578_; uint8_t v___x_2579_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2574_);
lean_dec_ref_known(v___x_2573_, 1);
v___x_2575_ = lean_unsigned_to_nat(0u);
v___x_2576_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1));
v_arr_2577_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v___x_2576_, v_a_2574_);
lean_dec(v_a_2574_);
v___x_2578_ = lean_array_get_size(v_arr_2577_);
v___x_2579_ = lean_nat_dec_eq(v___x_2578_, v___x_2575_);
if (v___x_2579_ == 0)
{
lean_object* v___x_2580_; lean_object* v___x_2581_; uint8_t v___x_2582_; 
v___x_2580_ = lean_unsigned_to_nat(1u);
v___x_2581_ = lean_nat_sub(v___x_2578_, v___x_2580_);
v___x_2582_ = lean_nat_dec_le(v___x_2575_, v___x_2581_);
if (v___x_2582_ == 0)
{
lean_inc(v___x_2581_);
v___y_2551_ = v___x_2578_;
v___y_2552_ = v___x_2581_;
v___y_2553_ = v_arr_2577_;
v___y_2554_ = v___x_2581_;
goto v___jp_2550_;
}
else
{
v___y_2551_ = v___x_2578_;
v___y_2552_ = v___x_2581_;
v___y_2553_ = v_arr_2577_;
v___y_2554_ = v___x_2575_;
goto v___jp_2550_;
}
}
else
{
v___y_2541_ = v_arr_2577_;
goto v___jp_2540_;
}
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
v_a_2583_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v___x_2573_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2573_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v___y_2592_, v___y_2593_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object* v_t_2596_, lean_object* v_k_2597_, lean_object* v_fallback_2598_){
_start:
{
if (lean_obj_tag(v_t_2596_) == 0)
{
lean_object* v_k_2599_; lean_object* v_v_2600_; lean_object* v_l_2601_; lean_object* v_r_2602_; uint8_t v___x_2603_; 
v_k_2599_ = lean_ctor_get(v_t_2596_, 1);
v_v_2600_ = lean_ctor_get(v_t_2596_, 2);
v_l_2601_ = lean_ctor_get(v_t_2596_, 3);
v_r_2602_ = lean_ctor_get(v_t_2596_, 4);
v___x_2603_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2597_, v_k_2599_);
switch(v___x_2603_)
{
case 0:
{
v_t_2596_ = v_l_2601_;
goto _start;
}
case 1:
{
lean_inc(v_v_2600_);
return v_v_2600_;
}
default: 
{
v_t_2596_ = v_r_2602_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2598_);
return v_fallback_2598_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object* v_t_2606_, lean_object* v_k_2607_, lean_object* v_fallback_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_2606_, v_k_2607_, v_fallback_2608_);
lean_dec(v_fallback_2608_);
lean_dec(v_k_2607_);
lean_dec(v_t_2606_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object* v_as_2610_, size_t v_sz_2611_, size_t v_i_2612_, lean_object* v_b_2613_){
_start:
{
uint8_t v___x_2615_; 
v___x_2615_ = lean_usize_dec_lt(v_i_2612_, v_sz_2611_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2616_; 
v___x_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2616_, 0, v_b_2613_);
return v___x_2616_;
}
else
{
lean_object* v_a_2617_; lean_object* v_fst_2618_; lean_object* v_snd_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; size_t v___x_2624_; size_t v___x_2625_; 
v_a_2617_ = lean_array_uget_borrowed(v_as_2610_, v_i_2612_);
v_fst_2618_ = lean_ctor_get(v_a_2617_, 0);
v_snd_2619_ = lean_ctor_get(v_a_2617_, 1);
v___x_2620_ = l_Lean_NameSet_empty;
v___x_2621_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_2613_, v_snd_2619_, v___x_2620_);
lean_inc(v_fst_2618_);
v___x_2622_ = l_Lean_NameSet_insert(v___x_2621_, v_fst_2618_);
lean_inc(v_snd_2619_);
v___x_2623_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_snd_2619_, v___x_2622_, v_b_2613_);
v___x_2624_ = ((size_t)1ULL);
v___x_2625_ = lean_usize_add(v_i_2612_, v___x_2624_);
v_i_2612_ = v___x_2625_;
v_b_2613_ = v___x_2623_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object* v_as_2627_, lean_object* v_sz_2628_, lean_object* v_i_2629_, lean_object* v_b_2630_, lean_object* v___y_2631_){
_start:
{
size_t v_sz_boxed_2632_; size_t v_i_boxed_2633_; lean_object* v_res_2634_; 
v_sz_boxed_2632_ = lean_unbox_usize(v_sz_2628_);
lean_dec(v_sz_2628_);
v_i_boxed_2633_ = lean_unbox_usize(v_i_2629_);
lean_dec(v_i_2629_);
v_res_2634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_2627_, v_sz_boxed_2632_, v_i_boxed_2633_, v_b_2630_);
lean_dec_ref(v_as_2627_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object* v_as_2635_, size_t v_sz_2636_, size_t v_i_2637_, lean_object* v_b_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
uint8_t v___x_2642_; 
v___x_2642_ = lean_usize_dec_lt(v_i_2637_, v_sz_2636_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2643_; 
v___x_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2643_, 0, v_b_2638_);
return v___x_2643_;
}
else
{
lean_object* v_a_2644_; size_t v_sz_2645_; size_t v___x_2646_; lean_object* v___x_2647_; 
v_a_2644_ = lean_array_uget_borrowed(v_as_2635_, v_i_2637_);
v_sz_2645_ = lean_array_size(v_a_2644_);
v___x_2646_ = ((size_t)0ULL);
v___x_2647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_a_2644_, v_sz_2645_, v___x_2646_, v_b_2638_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_a_2648_; size_t v___x_2649_; size_t v___x_2650_; 
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2648_);
lean_dec_ref_known(v___x_2647_, 1);
v___x_2649_ = ((size_t)1ULL);
v___x_2650_ = lean_usize_add(v_i_2637_, v___x_2649_);
v_i_2637_ = v___x_2650_;
v_b_2638_ = v_a_2648_;
goto _start;
}
else
{
return v___x_2647_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object* v_as_2652_, lean_object* v_sz_2653_, lean_object* v_i_2654_, lean_object* v_b_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
size_t v_sz_boxed_2659_; size_t v_i_boxed_2660_; lean_object* v_res_2661_; 
v_sz_boxed_2659_ = lean_unbox_usize(v_sz_2653_);
lean_dec(v_sz_2653_);
v_i_boxed_2660_ = lean_unbox_usize(v_i_2654_);
lean_dec(v_i_2654_);
v_res_2661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v_as_2652_, v_sz_boxed_2659_, v_i_boxed_2660_, v_b_2655_, v___y_2656_, v___y_2657_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec_ref(v_as_2652_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object* v_as_2662_, size_t v_i_2663_, size_t v_stop_2664_, lean_object* v_b_2665_){
_start:
{
uint8_t v___x_2666_; 
v___x_2666_ = lean_usize_dec_eq(v_i_2663_, v_stop_2664_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; lean_object* v_fst_2668_; lean_object* v_snd_2669_; lean_object* v___x_2670_; size_t v___x_2671_; size_t v___x_2672_; 
v___x_2667_ = lean_array_uget_borrowed(v_as_2662_, v_i_2663_);
v_fst_2668_ = lean_ctor_get(v___x_2667_, 0);
v_snd_2669_ = lean_ctor_get(v___x_2667_, 1);
lean_inc(v_snd_2669_);
lean_inc(v_fst_2668_);
v___x_2670_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2668_, v_snd_2669_, v_b_2665_);
v___x_2671_ = ((size_t)1ULL);
v___x_2672_ = lean_usize_add(v_i_2663_, v___x_2671_);
v_i_2663_ = v___x_2672_;
v_b_2665_ = v___x_2670_;
goto _start;
}
else
{
return v_b_2665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object* v_as_2674_, lean_object* v_i_2675_, lean_object* v_stop_2676_, lean_object* v_b_2677_){
_start:
{
size_t v_i_boxed_2678_; size_t v_stop_boxed_2679_; lean_object* v_res_2680_; 
v_i_boxed_2678_ = lean_unbox_usize(v_i_2675_);
lean_dec(v_i_2675_);
v_stop_boxed_2679_ = lean_unbox_usize(v_stop_2676_);
lean_dec(v_stop_2676_);
v_res_2680_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v_as_2674_, v_i_boxed_2678_, v_stop_boxed_2679_, v_b_2677_);
lean_dec_ref(v_as_2674_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object* v_as_2681_, size_t v_i_2682_, size_t v_stop_2683_, lean_object* v_b_2684_){
_start:
{
lean_object* v___y_2686_; uint8_t v___x_2690_; 
v___x_2690_ = lean_usize_dec_eq(v_i_2682_, v_stop_2683_);
if (v___x_2690_ == 0)
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; 
v___x_2691_ = lean_array_uget_borrowed(v_as_2681_, v_i_2682_);
v___x_2692_ = lean_unsigned_to_nat(0u);
v___x_2693_ = lean_array_get_size(v___x_2691_);
v___x_2694_ = lean_nat_dec_lt(v___x_2692_, v___x_2693_);
if (v___x_2694_ == 0)
{
v___y_2686_ = v_b_2684_;
goto v___jp_2685_;
}
else
{
uint8_t v___x_2695_; 
v___x_2695_ = lean_nat_dec_le(v___x_2693_, v___x_2693_);
if (v___x_2695_ == 0)
{
if (v___x_2694_ == 0)
{
v___y_2686_ = v_b_2684_;
goto v___jp_2685_;
}
else
{
size_t v___x_2696_; size_t v___x_2697_; lean_object* v___x_2698_; 
v___x_2696_ = ((size_t)0ULL);
v___x_2697_ = lean_usize_of_nat(v___x_2693_);
v___x_2698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_2691_, v___x_2696_, v___x_2697_, v_b_2684_);
v___y_2686_ = v___x_2698_;
goto v___jp_2685_;
}
}
else
{
size_t v___x_2699_; size_t v___x_2700_; lean_object* v___x_2701_; 
v___x_2699_ = ((size_t)0ULL);
v___x_2700_ = lean_usize_of_nat(v___x_2693_);
v___x_2701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_2691_, v___x_2699_, v___x_2700_, v_b_2684_);
v___y_2686_ = v___x_2701_;
goto v___jp_2685_;
}
}
}
else
{
return v_b_2684_;
}
v___jp_2685_:
{
size_t v___x_2687_; size_t v___x_2688_; 
v___x_2687_ = ((size_t)1ULL);
v___x_2688_ = lean_usize_add(v_i_2682_, v___x_2687_);
v_i_2682_ = v___x_2688_;
v_b_2684_ = v___y_2686_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object* v_as_2702_, lean_object* v_i_2703_, lean_object* v_stop_2704_, lean_object* v_b_2705_){
_start:
{
size_t v_i_boxed_2706_; size_t v_stop_boxed_2707_; lean_object* v_res_2708_; 
v_i_boxed_2706_ = lean_unbox_usize(v_i_2703_);
lean_dec(v_i_2703_);
v_stop_boxed_2707_ = lean_unbox_usize(v_stop_2704_);
lean_dec(v_stop_2704_);
v_res_2708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v_as_2702_, v_i_boxed_2706_, v_stop_boxed_2707_, v_b_2705_);
lean_dec_ref(v_as_2702_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object* v___y_2709_){
_start:
{
lean_object* v___x_2711_; lean_object* v_env_2712_; lean_object* v___x_2713_; lean_object* v_ext_2714_; lean_object* v_toEnvExtension_2715_; lean_object* v_asyncMode_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v_categories_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2711_ = lean_st_ref_get(v___y_2709_);
v_env_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc_ref_n(v_env_2712_, 2);
lean_dec(v___x_2711_);
v___x_2713_ = l_Lean_Parser_parserExtension;
v_ext_2714_ = lean_ctor_get(v___x_2713_, 1);
v_toEnvExtension_2715_ = lean_ctor_get(v_ext_2714_, 0);
v_asyncMode_2716_ = lean_ctor_get(v_toEnvExtension_2715_, 2);
v___x_2717_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2718_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2717_, v___x_2713_, v_env_2712_, v_asyncMode_2716_);
v_categories_2719_ = lean_ctor_get(v___x_2718_, 2);
lean_inc_ref(v_categories_2719_);
lean_dec(v___x_2718_);
v___x_2720_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_2721_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_2719_, v___x_2720_);
lean_dec_ref(v_categories_2719_);
if (lean_obj_tag(v___x_2721_) == 1)
{
lean_object* v_val_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2759_; 
v_val_2722_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2724_ = v___x_2721_;
v_isShared_2725_ = v_isSharedCheck_2759_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_val_2722_);
lean_dec(v___x_2721_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2759_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___y_2727_; lean_object* v___x_2736_; lean_object* v_toEnvExtension_2737_; lean_object* v_exportEntriesFn_2738_; lean_object* v_asyncMode_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v_importedEntries_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v_exported_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; uint8_t v___x_2751_; 
v___x_2736_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_2737_ = lean_ctor_get(v___x_2736_, 0);
v_exportEntriesFn_2738_ = lean_ctor_get(v___x_2736_, 4);
v_asyncMode_2739_ = lean_ctor_get(v_toEnvExtension_2737_, 2);
v___x_2740_ = lean_box(1);
v___x_2741_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_2742_ = lean_box(0);
lean_inc_ref_n(v_env_2712_, 2);
v___x_2743_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2741_, v_toEnvExtension_2737_, v_env_2712_, v_asyncMode_2739_, v___x_2742_);
v_importedEntries_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc_ref(v_importedEntries_2744_);
lean_dec(v___x_2743_);
v___x_2745_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2740_, v___x_2736_, v_env_2712_, v_asyncMode_2739_, v___x_2742_);
lean_inc_ref(v_exportEntriesFn_2738_);
v___x_2746_ = lean_apply_2(v_exportEntriesFn_2738_, v_env_2712_, v___x_2745_);
v_exported_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_exported_2747_);
lean_dec_ref(v___x_2746_);
v___x_2748_ = lean_array_push(v_importedEntries_2744_, v_exported_2747_);
v___x_2749_ = lean_unsigned_to_nat(0u);
v___x_2750_ = lean_array_get_size(v___x_2748_);
v___x_2751_ = lean_nat_dec_lt(v___x_2749_, v___x_2750_);
if (v___x_2751_ == 0)
{
lean_dec_ref(v___x_2748_);
v___y_2727_ = v___x_2740_;
goto v___jp_2726_;
}
else
{
uint8_t v___x_2752_; 
v___x_2752_ = lean_nat_dec_le(v___x_2750_, v___x_2750_);
if (v___x_2752_ == 0)
{
if (v___x_2751_ == 0)
{
lean_dec_ref(v___x_2748_);
v___y_2727_ = v___x_2740_;
goto v___jp_2726_;
}
else
{
size_t v___x_2753_; size_t v___x_2754_; lean_object* v___x_2755_; 
v___x_2753_ = ((size_t)0ULL);
v___x_2754_ = lean_usize_of_nat(v___x_2750_);
v___x_2755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_2748_, v___x_2753_, v___x_2754_, v___x_2740_);
lean_dec_ref(v___x_2748_);
v___y_2727_ = v___x_2755_;
goto v___jp_2726_;
}
}
else
{
size_t v___x_2756_; size_t v___x_2757_; lean_object* v___x_2758_; 
v___x_2756_ = ((size_t)0ULL);
v___x_2757_ = lean_usize_of_nat(v___x_2750_);
v___x_2758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_2748_, v___x_2756_, v___x_2757_, v___x_2740_);
lean_dec_ref(v___x_2748_);
v___y_2727_ = v___x_2758_;
goto v___jp_2726_;
}
}
v___jp_2726_:
{
lean_object* v_tables_2728_; lean_object* v_leadingTable_2729_; lean_object* v_trailingTable_2730_; lean_object* v_firstTokens_2731_; lean_object* v_firstTokens_2732_; lean_object* v___x_2734_; 
v_tables_2728_ = lean_ctor_get(v_val_2722_, 2);
v_leadingTable_2729_ = lean_ctor_get(v_tables_2728_, 0);
v_trailingTable_2730_ = lean_ctor_get(v_tables_2728_, 2);
lean_inc(v_trailingTable_2730_);
lean_inc(v_leadingTable_2729_);
lean_inc(v_val_2722_);
v_firstTokens_2731_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2722_, v_leadingTable_2729_, v___y_2727_);
v_firstTokens_2732_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2722_, v_trailingTable_2730_, v_firstTokens_2731_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set_tag(v___x_2724_, 0);
lean_ctor_set(v___x_2724_, 0, v_firstTokens_2732_);
v___x_2734_ = v___x_2724_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_firstTokens_2732_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
else
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
lean_dec(v___x_2721_);
lean_dec_ref(v_env_2712_);
v___x_2760_ = lean_box(1);
v___x_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2760_);
return v___x_2761_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_2762_);
lean_dec(v___y_2762_);
return v_res_2764_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0(void){
_start:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = lean_box(1);
v___x_2766_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2765_);
return v___x_2766_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1));
v___x_2769_ = l_Lean_stringToMessageData(v___x_2768_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object* v_a_2770_, lean_object* v_a_2771_){
_start:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v_env_2776_; lean_object* v_env_2777_; lean_object* v_env_2778_; lean_object* v___x_2779_; lean_object* v_toEnvExtension_2780_; lean_object* v_exportEntriesFn_2781_; lean_object* v_asyncMode_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v_importedEntries_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2839_; 
v___x_2773_ = lean_st_ref_get(v_a_2771_);
v___x_2774_ = lean_st_ref_get(v_a_2771_);
v___x_2775_ = lean_st_ref_get(v_a_2771_);
v_env_2776_ = lean_ctor_get(v___x_2773_, 0);
lean_inc_ref(v_env_2776_);
lean_dec(v___x_2773_);
v_env_2777_ = lean_ctor_get(v___x_2774_, 0);
lean_inc_ref(v_env_2777_);
lean_dec(v___x_2774_);
v_env_2778_ = lean_ctor_get(v___x_2775_, 0);
lean_inc_ref(v_env_2778_);
lean_dec(v___x_2775_);
v___x_2779_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_2780_ = lean_ctor_get(v___x_2779_, 0);
v_exportEntriesFn_2781_ = lean_ctor_get(v___x_2779_, 4);
v_asyncMode_2782_ = lean_ctor_get(v_toEnvExtension_2780_, 2);
v___x_2783_ = lean_box(1);
v___x_2784_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_2785_ = lean_box(0);
v___x_2786_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2784_, v_toEnvExtension_2780_, v_env_2776_, v_asyncMode_2782_, v___x_2785_);
v_importedEntries_2787_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2839_ == 0)
{
lean_object* v_unused_2840_; 
v_unused_2840_ = lean_ctor_get(v___x_2786_, 1);
lean_dec(v_unused_2840_);
v___x_2789_ = v___x_2786_;
v_isShared_2790_ = v_isSharedCheck_2839_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_importedEntries_2787_);
lean_dec(v___x_2786_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2839_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v_exported_2793_; lean_object* v___x_2794_; size_t v_sz_2795_; size_t v___x_2796_; lean_object* v___x_2797_; 
v___x_2791_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2783_, v___x_2779_, v_env_2778_, v_asyncMode_2782_, v___x_2785_);
lean_inc_ref(v_exportEntriesFn_2781_);
v___x_2792_ = lean_apply_2(v_exportEntriesFn_2781_, v_env_2777_, v___x_2791_);
v_exported_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_exported_2793_);
lean_dec_ref(v___x_2792_);
v___x_2794_ = lean_array_push(v_importedEntries_2787_, v_exported_2793_);
v_sz_2795_ = lean_array_size(v___x_2794_);
v___x_2796_ = ((size_t)0ULL);
v___x_2797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v___x_2794_, v_sz_2795_, v___x_2796_, v___x_2783_, v_a_2770_, v_a_2771_);
lean_dec_ref(v___x_2794_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v___x_2799_; lean_object* v_a_2800_; lean_object* v___x_2801_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
lean_dec_ref_known(v___x_2797_, 1);
v___x_2799_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v_a_2771_);
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref(v___x_2799_);
v___x_2801_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v_a_2770_, v_a_2771_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref_known(v___x_2801_, 1);
v___x_2803_ = lean_box(0);
v___x_2804_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_2800_, v_a_2798_, v_a_2802_, v___x_2803_, v_a_2770_, v_a_2771_);
lean_dec(v_a_2798_);
lean_dec(v_a_2800_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v_a_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2810_; 
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2805_);
lean_dec_ref_known(v___x_2804_, 1);
v___x_2806_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2);
v___x_2807_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2808_ = l_Lean_MessageData_joinSep(v_a_2805_, v___x_2807_);
if (v_isShared_2790_ == 0)
{
lean_ctor_set_tag(v___x_2789_, 7);
lean_ctor_set(v___x_2789_, 1, v___x_2808_);
lean_ctor_set(v___x_2789_, 0, v___x_2807_);
v___x_2810_ = v___x_2789_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2807_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v___x_2808_);
v___x_2810_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2811_ = l_Lean_MessageData_nestD(v___x_2810_);
v___x_2812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2806_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
v___x_2813_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v___x_2812_, v_a_2770_, v_a_2771_);
return v___x_2813_;
}
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_del_object(v___x_2789_);
v_a_2815_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2804_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2804_);
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
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_dec(v_a_2800_);
lean_dec(v_a_2798_);
lean_del_object(v___x_2789_);
v_a_2823_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2801_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2801_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
else
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
lean_del_object(v___x_2789_);
v_a_2831_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2797_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2797_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2831_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_2841_, v_a_2842_);
lean_dec(v_a_2842_);
lean_dec_ref(v_a_2841_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object* v___stx_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_){
_start:
{
lean_object* v___x_2849_; 
v___x_2849_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_2846_, v_a_2847_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object* v___stx_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_){
_start:
{
lean_object* v_res_2854_; 
v_res_2854_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags(v___stx_2850_, v_a_2851_, v_a_2852_);
lean_dec(v_a_2852_);
lean_dec_ref(v_a_2851_);
lean_dec(v___stx_2850_);
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object* v_00_u03b4_2855_, lean_object* v_t_2856_, lean_object* v_k_2857_, lean_object* v_fallback_2858_){
_start:
{
lean_object* v___x_2859_; 
v___x_2859_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_2856_, v_k_2857_, v_fallback_2858_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object* v_00_u03b4_2860_, lean_object* v_t_2861_, lean_object* v_k_2862_, lean_object* v_fallback_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(v_00_u03b4_2860_, v_t_2861_, v_k_2862_, v_fallback_2863_);
lean_dec(v_fallback_2863_);
lean_dec(v_k_2862_);
lean_dec(v_t_2861_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object* v_as_2865_, size_t v_sz_2866_, size_t v_i_2867_, lean_object* v_b_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v___x_2872_; 
v___x_2872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_2865_, v_sz_2866_, v_i_2867_, v_b_2868_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object* v_as_2873_, lean_object* v_sz_2874_, lean_object* v_i_2875_, lean_object* v_b_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
size_t v_sz_boxed_2880_; size_t v_i_boxed_2881_; lean_object* v_res_2882_; 
v_sz_boxed_2880_ = lean_unbox_usize(v_sz_2874_);
lean_dec(v_sz_2874_);
v_i_boxed_2881_ = lean_unbox_usize(v_i_2875_);
lean_dec(v_i_2875_);
v_res_2882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(v_as_2873_, v_sz_boxed_2880_, v_i_boxed_2881_, v_b_2876_, v___y_2877_, v___y_2878_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec_ref(v_as_2873_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v___x_2886_; 
v___x_2886_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_2884_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
lean_object* v_res_2890_; 
v_res_2890_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(v___y_2887_, v___y_2888_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object* v_val_2891_, lean_object* v___x_2892_, lean_object* v___x_2893_, lean_object* v_inst_2894_, lean_object* v_R_2895_, lean_object* v_a_2896_, lean_object* v_b_2897_){
_start:
{
lean_object* v___x_2898_; 
v___x_2898_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2891_, v___x_2892_, v___x_2893_, v_a_2896_, v_b_2897_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object* v_val_2899_, lean_object* v___x_2900_, lean_object* v___x_2901_, lean_object* v_inst_2902_, lean_object* v_R_2903_, lean_object* v_a_2904_, lean_object* v_b_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(v_val_2899_, v___x_2900_, v___x_2901_, v_inst_2902_, v_R_2903_, v_a_2904_, v_b_2905_);
lean_dec_ref(v___x_2900_);
lean_dec_ref(v_val_2899_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object* v_init_2907_, lean_object* v_t_2908_){
_start:
{
lean_object* v___x_2909_; 
v___x_2909_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_2907_, v_t_2908_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object* v_n_2910_, lean_object* v_as_2911_, lean_object* v_lo_2912_, lean_object* v_hi_2913_, lean_object* v_w_2914_, lean_object* v_hlo_2915_, lean_object* v_hhi_2916_){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_2910_, v_as_2911_, v_lo_2912_, v_hi_2913_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object* v_n_2918_, lean_object* v_as_2919_, lean_object* v_lo_2920_, lean_object* v_hi_2921_, lean_object* v_w_2922_, lean_object* v_hlo_2923_, lean_object* v_hhi_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(v_n_2918_, v_as_2919_, v_lo_2920_, v_hi_2921_, v_w_2922_, v_hlo_2923_, v_hhi_2924_);
lean_dec(v_hi_2921_);
lean_dec(v_n_2918_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object* v_00_u03b2_2926_, lean_object* v_x_2927_, lean_object* v_x_2928_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_2927_, v_x_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2930_, lean_object* v_x_2931_, lean_object* v_x_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(v_00_u03b2_2930_, v_x_2931_, v_x_2932_);
lean_dec(v_x_2932_);
lean_dec_ref(v_x_2931_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object* v_tac_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_2934_, v___y_2936_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object* v_tac_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(v_tac_2939_, v___y_2940_, v___y_2941_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object* v_00_u03b4_2944_, lean_object* v_t_2945_, lean_object* v_k_2946_){
_start:
{
lean_object* v___x_2947_; 
v___x_2947_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_2945_, v_k_2946_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___boxed(lean_object* v_00_u03b4_2948_, lean_object* v_t_2949_, lean_object* v_k_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(v_00_u03b4_2948_, v_t_2949_, v_k_2950_);
lean_dec(v_k_2950_);
lean_dec(v_t_2949_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object* v_00_u03b2_2952_, lean_object* v_x_2953_, lean_object* v_x_2954_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_2953_, v_x_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object* v_00_u03b2_2956_, lean_object* v_x_2957_, lean_object* v_x_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(v_00_u03b2_2956_, v_x_2957_, v_x_2958_);
lean_dec(v_x_2958_);
lean_dec_ref(v_x_2957_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(lean_object* v_n_2960_, lean_object* v_lo_2961_, lean_object* v_hi_2962_, lean_object* v_hhi_2963_, lean_object* v_pivot_2964_, lean_object* v_as_2965_, lean_object* v_i_2966_, lean_object* v_k_2967_, lean_object* v_ilo_2968_, lean_object* v_ik_2969_, lean_object* v_w_2970_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_2962_, v_pivot_2964_, v_as_2965_, v_i_2966_, v_k_2967_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___boxed(lean_object* v_n_2972_, lean_object* v_lo_2973_, lean_object* v_hi_2974_, lean_object* v_hhi_2975_, lean_object* v_pivot_2976_, lean_object* v_as_2977_, lean_object* v_i_2978_, lean_object* v_k_2979_, lean_object* v_ilo_2980_, lean_object* v_ik_2981_, lean_object* v_w_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(v_n_2972_, v_lo_2973_, v_hi_2974_, v_hhi_2975_, v_pivot_2976_, v_as_2977_, v_i_2978_, v_k_2979_, v_ilo_2980_, v_ik_2981_, v_w_2982_);
lean_dec(v_hi_2974_);
lean_dec(v_lo_2973_);
lean_dec(v_n_2972_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(lean_object* v_as_2984_, size_t v_sz_2985_, size_t v_i_2986_, lean_object* v_b_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_){
_start:
{
lean_object* v___x_2991_; 
v___x_2991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_2984_, v_sz_2985_, v_i_2986_, v_b_2987_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___boxed(lean_object* v_as_2992_, lean_object* v_sz_2993_, lean_object* v_i_2994_, lean_object* v_b_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
size_t v_sz_boxed_2999_; size_t v_i_boxed_3000_; lean_object* v_res_3001_; 
v_sz_boxed_2999_ = lean_unbox_usize(v_sz_2993_);
lean_dec(v_sz_2993_);
v_i_boxed_3000_ = lean_unbox_usize(v_i_2994_);
lean_dec(v_i_2994_);
v_res_3001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(v_as_2992_, v_sz_boxed_2999_, v_i_boxed_3000_, v_b_2995_, v___y_2996_, v___y_2997_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2996_);
lean_dec_ref(v_as_2992_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object* v_init_3002_, lean_object* v_t_3003_){
_start:
{
lean_object* v___x_3004_; 
v___x_3004_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_3002_, v_t_3003_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object* v_init_3005_, lean_object* v_t_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(v_init_3005_, v_t_3006_);
lean_dec(v_t_3006_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object* v_n_3008_, lean_object* v_as_3009_, lean_object* v_lo_3010_, lean_object* v_hi_3011_, lean_object* v_w_3012_, lean_object* v_hlo_3013_, lean_object* v_hhi_3014_){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_3008_, v_as_3009_, v_lo_3010_, v_hi_3011_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object* v_n_3016_, lean_object* v_as_3017_, lean_object* v_lo_3018_, lean_object* v_hi_3019_, lean_object* v_w_3020_, lean_object* v_hlo_3021_, lean_object* v_hhi_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(v_n_3016_, v_as_3017_, v_lo_3018_, v_hi_3019_, v_w_3020_, v_hlo_3021_, v_hhi_3022_);
lean_dec(v_hi_3019_);
lean_dec(v_n_3016_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object* v_init_3024_, lean_object* v_x_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
lean_object* v___x_3029_; 
v___x_3029_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_3024_, v_x_3025_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object* v_init_3030_, lean_object* v_x_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(v_init_3030_, v_x_3031_, v___y_3032_, v___y_3033_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_3036_, lean_object* v_x_3037_, size_t v_x_3038_, lean_object* v_x_3039_){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3037_, v_x_3038_, v_x_3039_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3041_, lean_object* v_x_3042_, lean_object* v_x_3043_, lean_object* v_x_3044_){
_start:
{
size_t v_x_19109__boxed_3045_; lean_object* v_res_3046_; 
v_x_19109__boxed_3045_ = lean_unbox_usize(v_x_3043_);
lean_dec(v_x_3043_);
v_res_3046_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(v_00_u03b2_3041_, v_x_3042_, v_x_19109__boxed_3045_, v_x_3044_);
lean_dec(v_x_3044_);
lean_dec_ref(v_x_3042_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object* v_as_3047_, lean_object* v_k_3048_, lean_object* v_x_3049_, lean_object* v_x_3050_, lean_object* v_x_3051_){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_3047_, v_k_3048_, v_x_3049_, v_x_3050_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object* v_as_3053_, lean_object* v_k_3054_, lean_object* v_x_3055_, lean_object* v_x_3056_, lean_object* v_x_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(v_as_3053_, v_k_3054_, v_x_3055_, v_x_3056_, v_x_3057_);
lean_dec_ref(v_k_3054_);
lean_dec_ref(v_as_3053_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(lean_object* v_00_u03b2_3059_, lean_object* v_m_3060_, lean_object* v_a_3061_){
_start:
{
lean_object* v___x_3062_; 
v___x_3062_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_3060_, v_a_3061_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___boxed(lean_object* v_00_u03b2_3063_, lean_object* v_m_3064_, lean_object* v_a_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(v_00_u03b2_3063_, v_m_3064_, v_a_3065_);
lean_dec(v_a_3065_);
lean_dec_ref(v_m_3064_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(lean_object* v_n_3067_, lean_object* v_lo_3068_, lean_object* v_hi_3069_, lean_object* v_hhi_3070_, lean_object* v_pivot_3071_, lean_object* v_as_3072_, lean_object* v_i_3073_, lean_object* v_k_3074_, lean_object* v_ilo_3075_, lean_object* v_ik_3076_, lean_object* v_w_3077_){
_start:
{
lean_object* v___x_3078_; 
v___x_3078_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_3069_, v_pivot_3071_, v_as_3072_, v_i_3073_, v_k_3074_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___boxed(lean_object* v_n_3079_, lean_object* v_lo_3080_, lean_object* v_hi_3081_, lean_object* v_hhi_3082_, lean_object* v_pivot_3083_, lean_object* v_as_3084_, lean_object* v_i_3085_, lean_object* v_k_3086_, lean_object* v_ilo_3087_, lean_object* v_ik_3088_, lean_object* v_w_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(v_n_3079_, v_lo_3080_, v_hi_3081_, v_hhi_3082_, v_pivot_3083_, v_as_3084_, v_i_3085_, v_k_3086_, v_ilo_3087_, v_ik_3088_, v_w_3089_);
lean_dec(v_hi_3081_);
lean_dec(v_lo_3080_);
lean_dec(v_n_3079_);
return v_res_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_3091_, lean_object* v_keys_3092_, lean_object* v_vals_3093_, lean_object* v_heq_3094_, lean_object* v_i_3095_, lean_object* v_k_3096_){
_start:
{
lean_object* v___x_3097_; 
v___x_3097_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_3092_, v_vals_3093_, v_i_3095_, v_k_3096_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object* v_00_u03b2_3098_, lean_object* v_keys_3099_, lean_object* v_vals_3100_, lean_object* v_heq_3101_, lean_object* v_i_3102_, lean_object* v_k_3103_){
_start:
{
lean_object* v_res_3104_; 
v_res_3104_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(v_00_u03b2_3098_, v_keys_3099_, v_vals_3100_, v_heq_3101_, v_i_3102_, v_k_3103_);
lean_dec(v_k_3103_);
lean_dec_ref(v_vals_3100_);
lean_dec_ref(v_keys_3099_);
return v_res_3104_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(lean_object* v_00_u03b2_3105_, lean_object* v_a_3106_, lean_object* v_x_3107_){
_start:
{
lean_object* v___x_3108_; 
v___x_3108_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_3106_, v_x_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___boxed(lean_object* v_00_u03b2_3109_, lean_object* v_a_3110_, lean_object* v_x_3111_){
_start:
{
lean_object* v_res_3112_; 
v_res_3112_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(v_00_u03b2_3109_, v_a_3110_, v_x_3111_);
lean_dec(v_x_3111_);
lean_dec(v_a_3110_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1(){
_start:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3127_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3128_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1));
v___x_3129_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3130_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed), 4, 0);
v___x_3131_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3127_, v___x_3128_, v___x_3129_, v___x_3130_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object* v_a_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3(){
_start:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3136_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3137_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0));
v___x_3138_ = l_Lean_addBuiltinDocString(v___x_3136_, v___x_3137_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object* v_a_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5(){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3167_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3168_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6));
v___x_3169_ = l_Lean_addBuiltinDeclarationRanges(v___x_3167_, v___x_3168_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object* v_a_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object* v_env_3172_, lean_object* v___x_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, uint8_t v_includeUnnamed_3176_, lean_object* v_x_3177_, lean_object* v_____s_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v_fst_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3239_; 
v_fst_3184_ = lean_ctor_get(v_x_3177_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v_x_3177_);
if (v_isSharedCheck_3239_ == 0)
{
lean_object* v_unused_3240_; 
v_unused_3240_ = lean_ctor_get(v_x_3177_, 1);
lean_dec(v_unused_3240_);
v___x_3186_ = v_x_3177_;
v_isShared_3187_ = v_isSharedCheck_3239_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_fst_3184_);
lean_dec(v_x_3177_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3239_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v_userName_3189_; lean_object* v___y_3190_; lean_object* v___x_3224_; 
lean_inc(v_fst_3184_);
lean_inc_ref(v_env_3172_);
v___x_3224_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_3172_, v_fst_3184_);
if (lean_obj_tag(v___x_3224_) == 1)
{
lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3232_; 
lean_del_object(v___x_3186_);
lean_dec(v_fst_3184_);
lean_dec(v___x_3173_);
lean_dec_ref(v_env_3172_);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3232_ == 0)
{
lean_object* v_unused_3233_; 
v_unused_3233_ = lean_ctor_get(v___x_3224_, 0);
lean_dec(v_unused_3233_);
v___x_3226_ = v___x_3224_;
v_isShared_3227_ = v_isSharedCheck_3232_;
goto v_resetjp_3225_;
}
else
{
lean_dec(v___x_3224_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3232_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 0, v_____s_3178_);
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_____s_3178_);
v___x_3229_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
lean_object* v___x_3230_; 
v___x_3230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3229_);
return v___x_3230_;
}
}
}
else
{
lean_object* v___x_3234_; 
lean_dec(v___x_3224_);
v___x_3234_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_a_3175_, v_fst_3184_);
if (lean_obj_tag(v___x_3234_) == 1)
{
lean_object* v_val_3235_; 
v_val_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_val_3235_);
lean_dec_ref_known(v___x_3234_, 1);
v_userName_3189_ = v_val_3235_;
v___y_3190_ = v___y_3181_;
goto v___jp_3188_;
}
else
{
lean_dec(v___x_3234_);
if (v_includeUnnamed_3176_ == 0)
{
lean_object* v___x_3236_; lean_object* v___x_3237_; 
lean_del_object(v___x_3186_);
lean_dec(v_fst_3184_);
lean_dec(v___x_3173_);
lean_dec_ref(v_env_3172_);
v___x_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3236_, 0, v_____s_3178_);
v___x_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3236_);
return v___x_3237_;
}
else
{
lean_object* v___x_3238_; 
lean_inc(v_fst_3184_);
v___x_3238_ = l_Lean_Name_toString(v_fst_3184_, v_includeUnnamed_3176_);
v_userName_3189_ = v___x_3238_;
v___y_3190_ = v___y_3181_;
goto v___jp_3188_;
}
}
}
v___jp_3188_:
{
uint8_t v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3191_ = 1;
v___x_3192_ = l_Lean_Options_empty;
v___x_3193_ = lean_box(0);
lean_inc(v_fst_3184_);
lean_inc_ref(v_env_3172_);
v___x_3194_ = l_Lean_findDocString_x3f(v_env_3172_, v_fst_3184_, v___x_3191_, v___x_3192_, v___x_3173_, v___x_3193_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3208_; 
lean_del_object(v___x_3186_);
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3197_ = v___x_3194_;
v_isShared_3198_ = v_isSharedCheck_3208_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3194_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3208_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3206_; 
v___x_3199_ = l_Lean_NameSet_empty;
v___x_3200_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_a_3174_, v_fst_3184_, v___x_3199_);
lean_inc(v_fst_3184_);
v___x_3201_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_3172_, v_fst_3184_);
v___x_3202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3202_, 0, v_fst_3184_);
lean_ctor_set(v___x_3202_, 1, v_userName_3189_);
lean_ctor_set(v___x_3202_, 2, v___x_3200_);
lean_ctor_set(v___x_3202_, 3, v_a_3195_);
lean_ctor_set(v___x_3202_, 4, v___x_3201_);
v___x_3203_ = lean_array_push(v_____s_3178_, v___x_3202_);
v___x_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 0, v___x_3204_);
v___x_3206_ = v___x_3197_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3204_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3223_; 
lean_dec_ref(v_userName_3189_);
lean_dec(v_fst_3184_);
lean_dec_ref(v_____s_3178_);
lean_dec_ref(v_env_3172_);
v_a_3209_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3211_ = v___x_3194_;
v_isShared_3212_ = v_isSharedCheck_3223_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3194_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3223_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v_ref_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3218_; 
v_ref_3213_ = lean_ctor_get(v___y_3190_, 5);
v___x_3214_ = lean_io_error_to_string(v_a_3209_);
v___x_3215_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
v___x_3216_ = l_Lean_MessageData_ofFormat(v___x_3215_);
lean_inc(v_ref_3213_);
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 1, v___x_3216_);
lean_ctor_set(v___x_3186_, 0, v_ref_3213_);
v___x_3218_ = v___x_3186_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_ref_3213_);
lean_ctor_set(v_reuseFailAlloc_3222_, 1, v___x_3216_);
v___x_3218_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
lean_object* v___x_3220_; 
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 0, v___x_3218_);
v___x_3220_ = v___x_3211_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3218_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object* v_env_3241_, lean_object* v___x_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_includeUnnamed_3245_, lean_object* v_x_3246_, lean_object* v_____s_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
uint8_t v_includeUnnamed_boxed_3253_; lean_object* v_res_3254_; 
v_includeUnnamed_boxed_3253_ = lean_unbox(v_includeUnnamed_3245_);
v_res_3254_ = l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(v_env_3241_, v___x_3242_, v_a_3243_, v_a_3244_, v_includeUnnamed_boxed_3253_, v_x_3246_, v_____s_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v_a_3244_);
lean_dec(v_a_3243_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object* v_as_3255_, size_t v_sz_3256_, size_t v_i_3257_, lean_object* v_b_3258_){
_start:
{
uint8_t v___x_3260_; 
v___x_3260_ = lean_usize_dec_lt(v_i_3257_, v_sz_3256_);
if (v___x_3260_ == 0)
{
lean_object* v___x_3261_; 
v___x_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3261_, 0, v_b_3258_);
return v___x_3261_;
}
else
{
lean_object* v_a_3262_; lean_object* v_fst_3263_; lean_object* v_snd_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; size_t v___x_3269_; size_t v___x_3270_; 
v_a_3262_ = lean_array_uget_borrowed(v_as_3255_, v_i_3257_);
v_fst_3263_ = lean_ctor_get(v_a_3262_, 0);
v_snd_3264_ = lean_ctor_get(v_a_3262_, 1);
v___x_3265_ = l_Lean_NameSet_empty;
v___x_3266_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_3258_, v_fst_3263_, v___x_3265_);
lean_inc(v_snd_3264_);
v___x_3267_ = l_Lean_NameSet_insert(v___x_3266_, v_snd_3264_);
lean_inc(v_fst_3263_);
v___x_3268_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3263_, v___x_3267_, v_b_3258_);
v___x_3269_ = ((size_t)1ULL);
v___x_3270_ = lean_usize_add(v_i_3257_, v___x_3269_);
v_i_3257_ = v___x_3270_;
v_b_3258_ = v___x_3268_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object* v_as_3272_, lean_object* v_sz_3273_, lean_object* v_i_3274_, lean_object* v_b_3275_, lean_object* v___y_3276_){
_start:
{
size_t v_sz_boxed_3277_; size_t v_i_boxed_3278_; lean_object* v_res_3279_; 
v_sz_boxed_3277_ = lean_unbox_usize(v_sz_3273_);
lean_dec(v_sz_3273_);
v_i_boxed_3278_ = lean_unbox_usize(v_i_3274_);
lean_dec(v_i_3274_);
v_res_3279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_3272_, v_sz_boxed_3277_, v_i_boxed_3278_, v_b_3275_);
lean_dec_ref(v_as_3272_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object* v_as_3280_, size_t v_sz_3281_, size_t v_i_3282_, lean_object* v_b_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
uint8_t v___x_3289_; 
v___x_3289_ = lean_usize_dec_lt(v_i_3282_, v_sz_3281_);
if (v___x_3289_ == 0)
{
lean_object* v___x_3290_; 
v___x_3290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3290_, 0, v_b_3283_);
return v___x_3290_;
}
else
{
lean_object* v_a_3291_; size_t v_sz_3292_; size_t v___x_3293_; lean_object* v___x_3294_; 
v_a_3291_ = lean_array_uget_borrowed(v_as_3280_, v_i_3282_);
v_sz_3292_ = lean_array_size(v_a_3291_);
v___x_3293_ = ((size_t)0ULL);
v___x_3294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_a_3291_, v_sz_3292_, v___x_3293_, v_b_3283_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; size_t v___x_3296_; size_t v___x_3297_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
lean_inc(v_a_3295_);
lean_dec_ref_known(v___x_3294_, 1);
v___x_3296_ = ((size_t)1ULL);
v___x_3297_ = lean_usize_add(v_i_3282_, v___x_3296_);
v_i_3282_ = v___x_3297_;
v_b_3283_ = v_a_3295_;
goto _start;
}
else
{
return v___x_3294_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object* v_as_3299_, lean_object* v_sz_3300_, lean_object* v_i_3301_, lean_object* v_b_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
size_t v_sz_boxed_3308_; size_t v_i_boxed_3309_; lean_object* v_res_3310_; 
v_sz_boxed_3308_ = lean_unbox_usize(v_sz_3300_);
lean_dec(v_sz_3300_);
v_i_boxed_3309_ = lean_unbox_usize(v_i_3301_);
lean_dec(v_i_3301_);
v_res_3310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v_as_3299_, v_sz_boxed_3308_, v_i_boxed_3309_, v_b_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec_ref(v_as_3299_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object* v_f_3311_, lean_object* v_keys_3312_, lean_object* v_vals_3313_, lean_object* v_i_3314_, lean_object* v_acc_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
lean_object* v___x_3321_; uint8_t v___x_3322_; 
v___x_3321_ = lean_array_get_size(v_keys_3312_);
v___x_3322_ = lean_nat_dec_lt(v_i_3314_, v___x_3321_);
if (v___x_3322_ == 0)
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
lean_dec(v_i_3314_);
lean_dec_ref(v_f_3311_);
v___x_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3323_, 0, v_acc_3315_);
v___x_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
return v___x_3324_;
}
else
{
lean_object* v_k_3325_; lean_object* v_v_3326_; lean_object* v___x_3327_; 
v_k_3325_ = lean_array_fget_borrowed(v_keys_3312_, v_i_3314_);
v_v_3326_ = lean_array_fget_borrowed(v_vals_3313_, v_i_3314_);
lean_inc_ref(v_f_3311_);
lean_inc(v___y_3319_);
lean_inc_ref(v___y_3318_);
lean_inc(v___y_3317_);
lean_inc_ref(v___y_3316_);
lean_inc(v_v_3326_);
lean_inc(v_k_3325_);
v___x_3327_ = lean_apply_8(v_f_3311_, v_acc_3315_, v_k_3325_, v_v_3326_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, lean_box(0));
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_a_3328_);
if (lean_obj_tag(v_a_3328_) == 0)
{
lean_dec_ref_known(v_a_3328_, 1);
lean_dec(v_i_3314_);
lean_dec_ref(v_f_3311_);
return v___x_3327_;
}
else
{
lean_object* v_a_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
lean_dec_ref_known(v___x_3327_, 1);
v_a_3329_ = lean_ctor_get(v_a_3328_, 0);
lean_inc(v_a_3329_);
lean_dec_ref_known(v_a_3328_, 1);
v___x_3330_ = lean_unsigned_to_nat(1u);
v___x_3331_ = lean_nat_add(v_i_3314_, v___x_3330_);
lean_dec(v_i_3314_);
v_i_3314_ = v___x_3331_;
v_acc_3315_ = v_a_3329_;
goto _start;
}
}
else
{
lean_dec(v_i_3314_);
lean_dec_ref(v_f_3311_);
return v___x_3327_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_f_3333_, lean_object* v_keys_3334_, lean_object* v_vals_3335_, lean_object* v_i_3336_, lean_object* v_acc_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3333_, v_keys_3334_, v_vals_3335_, v_i_3336_, v_acc_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec_ref(v_vals_3335_);
lean_dec_ref(v_keys_3334_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object* v_f_3344_, lean_object* v_x_3345_, lean_object* v_x_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
if (lean_obj_tag(v_x_3345_) == 0)
{
lean_object* v_es_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3374_; 
v_es_3352_ = lean_ctor_get(v_x_3345_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v_x_3345_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3354_ = v_x_3345_;
v_isShared_3355_ = v_isSharedCheck_3374_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_es_3352_);
lean_dec(v_x_3345_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3374_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; 
v___x_3356_ = lean_unsigned_to_nat(0u);
v___x_3357_ = lean_array_get_size(v_es_3352_);
v___x_3358_ = lean_nat_dec_lt(v___x_3356_, v___x_3357_);
if (v___x_3358_ == 0)
{
lean_object* v___x_3360_; 
lean_dec_ref(v_es_3352_);
lean_dec_ref(v_f_3344_);
if (v_isShared_3355_ == 0)
{
lean_ctor_set_tag(v___x_3354_, 1);
lean_ctor_set(v___x_3354_, 0, v_x_3346_);
v___x_3360_ = v___x_3354_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_x_3346_);
v___x_3360_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
lean_object* v___x_3361_; 
v___x_3361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3360_);
return v___x_3361_;
}
}
else
{
uint8_t v___x_3363_; 
v___x_3363_ = lean_nat_dec_le(v___x_3357_, v___x_3357_);
if (v___x_3363_ == 0)
{
if (v___x_3358_ == 0)
{
lean_object* v___x_3365_; 
lean_dec_ref(v_es_3352_);
lean_dec_ref(v_f_3344_);
if (v_isShared_3355_ == 0)
{
lean_ctor_set_tag(v___x_3354_, 1);
lean_ctor_set(v___x_3354_, 0, v_x_3346_);
v___x_3365_ = v___x_3354_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_x_3346_);
v___x_3365_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
lean_object* v___x_3366_; 
v___x_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
return v___x_3366_;
}
}
else
{
size_t v___x_3368_; size_t v___x_3369_; lean_object* v___x_3370_; 
lean_del_object(v___x_3354_);
v___x_3368_ = ((size_t)0ULL);
v___x_3369_ = lean_usize_of_nat(v___x_3357_);
v___x_3370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3344_, v_es_3352_, v___x_3368_, v___x_3369_, v_x_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
lean_dec_ref(v_es_3352_);
return v___x_3370_;
}
}
else
{
size_t v___x_3371_; size_t v___x_3372_; lean_object* v___x_3373_; 
lean_del_object(v___x_3354_);
v___x_3371_ = ((size_t)0ULL);
v___x_3372_ = lean_usize_of_nat(v___x_3357_);
v___x_3373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3344_, v_es_3352_, v___x_3371_, v___x_3372_, v_x_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
lean_dec_ref(v_es_3352_);
return v___x_3373_;
}
}
}
}
else
{
lean_object* v_ks_3375_; lean_object* v_vs_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v_ks_3375_ = lean_ctor_get(v_x_3345_, 0);
lean_inc_ref(v_ks_3375_);
v_vs_3376_ = lean_ctor_get(v_x_3345_, 1);
lean_inc_ref(v_vs_3376_);
lean_dec_ref_known(v_x_3345_, 2);
v___x_3377_ = lean_unsigned_to_nat(0u);
v___x_3378_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3344_, v_ks_3375_, v_vs_3376_, v___x_3377_, v_x_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
lean_dec_ref(v_vs_3376_);
lean_dec_ref(v_ks_3375_);
return v___x_3378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_f_3379_, lean_object* v_as_3380_, size_t v_i_3381_, size_t v_stop_3382_, lean_object* v_b_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
lean_object* v_a_3390_; lean_object* v___y_3395_; uint8_t v___x_3398_; 
v___x_3398_ = lean_usize_dec_eq(v_i_3381_, v_stop_3382_);
if (v___x_3398_ == 0)
{
lean_object* v___x_3399_; 
v___x_3399_ = lean_array_uget_borrowed(v_as_3380_, v_i_3381_);
switch(lean_obj_tag(v___x_3399_))
{
case 0:
{
lean_object* v_key_3400_; lean_object* v_val_3401_; lean_object* v___x_3402_; 
v_key_3400_ = lean_ctor_get(v___x_3399_, 0);
v_val_3401_ = lean_ctor_get(v___x_3399_, 1);
lean_inc_ref(v_f_3379_);
lean_inc(v___y_3387_);
lean_inc_ref(v___y_3386_);
lean_inc(v___y_3385_);
lean_inc_ref(v___y_3384_);
lean_inc(v_val_3401_);
lean_inc(v_key_3400_);
v___x_3402_ = lean_apply_8(v_f_3379_, v_b_3383_, v_key_3400_, v_val_3401_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, lean_box(0));
v___y_3395_ = v___x_3402_;
goto v___jp_3394_;
}
case 1:
{
lean_object* v_node_3403_; lean_object* v___x_3404_; 
v_node_3403_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_node_3403_);
lean_inc_ref(v_f_3379_);
v___x_3404_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3379_, v_node_3403_, v_b_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
v___y_3395_ = v___x_3404_;
goto v___jp_3394_;
}
default: 
{
v_a_3390_ = v_b_3383_;
goto v___jp_3389_;
}
}
}
else
{
lean_object* v___x_3405_; lean_object* v___x_3406_; 
lean_dec_ref(v_f_3379_);
v___x_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3405_, 0, v_b_3383_);
v___x_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3405_);
return v___x_3406_;
}
v___jp_3389_:
{
size_t v___x_3391_; size_t v___x_3392_; 
v___x_3391_ = ((size_t)1ULL);
v___x_3392_ = lean_usize_add(v_i_3381_, v___x_3391_);
v_i_3381_ = v___x_3392_;
v_b_3383_ = v_a_3390_;
goto _start;
}
v___jp_3394_:
{
if (lean_obj_tag(v___y_3395_) == 0)
{
lean_object* v_a_3396_; 
v_a_3396_ = lean_ctor_get(v___y_3395_, 0);
if (lean_obj_tag(v_a_3396_) == 0)
{
lean_dec_ref(v_f_3379_);
return v___y_3395_;
}
else
{
lean_object* v_a_3397_; 
lean_inc_ref(v_a_3396_);
lean_dec_ref_known(v___y_3395_, 1);
v_a_3397_ = lean_ctor_get(v_a_3396_, 0);
lean_inc(v_a_3397_);
lean_dec_ref_known(v_a_3396_, 1);
v_a_3390_ = v_a_3397_;
goto v___jp_3389_;
}
}
else
{
lean_dec_ref(v_f_3379_);
return v___y_3395_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_3407_, lean_object* v_as_3408_, lean_object* v_i_3409_, lean_object* v_stop_3410_, lean_object* v_b_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
size_t v_i_boxed_3417_; size_t v_stop_boxed_3418_; lean_object* v_res_3419_; 
v_i_boxed_3417_ = lean_unbox_usize(v_i_3409_);
lean_dec(v_i_3409_);
v_stop_boxed_3418_ = lean_unbox_usize(v_stop_3410_);
lean_dec(v_stop_3410_);
v_res_3419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3407_, v_as_3408_, v_i_boxed_3417_, v_stop_boxed_3418_, v_b_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec_ref(v_as_3408_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_f_3420_, lean_object* v_x_3421_, lean_object* v_x_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3420_, v_x_3421_, v_x_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object* v_f_3429_, lean_object* v_s_3430_, lean_object* v_a_3431_, lean_object* v_b_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3438_, 0, v_a_3431_);
lean_ctor_set(v___x_3438_, 1, v_b_3432_);
lean_inc(v___y_3436_);
lean_inc_ref(v___y_3435_);
lean_inc(v___y_3434_);
lean_inc_ref(v___y_3433_);
v___x_3439_ = lean_apply_7(v_f_3429_, v___x_3438_, v_s_3430_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, lean_box(0));
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3466_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3442_ = v___x_3439_;
v_isShared_3443_ = v_isSharedCheck_3466_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3439_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3466_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
if (lean_obj_tag(v_a_3440_) == 0)
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3454_; 
v_a_3444_ = lean_ctor_get(v_a_3440_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v_a_3440_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3446_ = v_a_3440_;
v_isShared_3447_ = v_isSharedCheck_3454_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v_a_3440_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3454_;
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
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3444_);
v___x_3449_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
lean_object* v___x_3451_; 
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 0, v___x_3449_);
v___x_3451_ = v___x_3442_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3449_);
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
else
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3465_; 
v_a_3455_ = lean_ctor_get(v_a_3440_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v_a_3440_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3457_ = v_a_3440_;
v_isShared_3458_ = v_isSharedCheck_3465_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v_a_3440_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3465_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3460_; 
if (v_isShared_3458_ == 0)
{
v___x_3460_ = v___x_3457_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3455_);
v___x_3460_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
lean_object* v___x_3462_; 
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 0, v___x_3460_);
v___x_3462_ = v___x_3442_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
}
}
else
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3474_; 
v_a_3467_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3469_ = v___x_3439_;
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3439_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3472_; 
if (v_isShared_3470_ == 0)
{
v___x_3472_ = v___x_3469_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_a_3467_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object* v_f_3475_, lean_object* v_s_3476_, lean_object* v_a_3477_, lean_object* v_b_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(v_f_3475_, v_s_3476_, v_a_3477_, v_b_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object* v_map_3485_, lean_object* v_init_3486_, lean_object* v_f_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
lean_object* v___f_3493_; lean_object* v___x_3494_; 
v___f_3493_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3493_, 0, v_f_3487_);
lean_inc_ref(v_map_3485_);
v___x_3494_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v___f_3493_, v_map_3485_, v_init_3486_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3503_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3497_ = v___x_3494_;
v_isShared_3498_ = v_isSharedCheck_3503_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3494_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3503_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v_a_3499_; lean_object* v___x_3501_; 
v_a_3499_ = lean_ctor_get(v_a_3495_, 0);
lean_inc(v_a_3499_);
lean_dec(v_a_3495_);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v_a_3499_);
v___x_3501_ = v___x_3497_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3499_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
v_a_3504_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3494_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3494_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3509_; 
if (v_isShared_3507_ == 0)
{
v___x_3509_ = v___x_3506_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object* v_map_3512_, lean_object* v_init_3513_, lean_object* v_f_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_3512_, v_init_3513_, v_f_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec_ref(v_map_3512_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object* v___y_3521_){
_start:
{
lean_object* v___x_3523_; lean_object* v_env_3524_; lean_object* v___x_3525_; lean_object* v_ext_3526_; lean_object* v_toEnvExtension_3527_; lean_object* v_asyncMode_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v_categories_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3523_ = lean_st_ref_get(v___y_3521_);
v_env_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc_ref_n(v_env_3524_, 2);
lean_dec(v___x_3523_);
v___x_3525_ = l_Lean_Parser_parserExtension;
v_ext_3526_ = lean_ctor_get(v___x_3525_, 1);
v_toEnvExtension_3527_ = lean_ctor_get(v_ext_3526_, 0);
v_asyncMode_3528_ = lean_ctor_get(v_toEnvExtension_3527_, 2);
v___x_3529_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3530_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3529_, v___x_3525_, v_env_3524_, v_asyncMode_3528_);
v_categories_3531_ = lean_ctor_get(v___x_3530_, 2);
lean_inc_ref(v_categories_3531_);
lean_dec(v___x_3530_);
v___x_3532_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3533_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3531_, v___x_3532_);
lean_dec_ref(v_categories_3531_);
if (lean_obj_tag(v___x_3533_) == 1)
{
lean_object* v_val_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3571_; 
v_val_3534_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3536_ = v___x_3533_;
v_isShared_3537_ = v_isSharedCheck_3571_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_val_3534_);
lean_dec(v___x_3533_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3571_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___y_3539_; lean_object* v___x_3548_; lean_object* v_toEnvExtension_3549_; lean_object* v_exportEntriesFn_3550_; lean_object* v_asyncMode_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v_importedEntries_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v_exported_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; uint8_t v___x_3563_; 
v___x_3548_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3549_ = lean_ctor_get(v___x_3548_, 0);
v_exportEntriesFn_3550_ = lean_ctor_get(v___x_3548_, 4);
v_asyncMode_3551_ = lean_ctor_get(v_toEnvExtension_3549_, 2);
v___x_3552_ = lean_box(1);
v___x_3553_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3554_ = lean_box(0);
lean_inc_ref_n(v_env_3524_, 2);
v___x_3555_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3553_, v_toEnvExtension_3549_, v_env_3524_, v_asyncMode_3551_, v___x_3554_);
v_importedEntries_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc_ref(v_importedEntries_3556_);
lean_dec(v___x_3555_);
v___x_3557_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3552_, v___x_3548_, v_env_3524_, v_asyncMode_3551_, v___x_3554_);
lean_inc_ref(v_exportEntriesFn_3550_);
v___x_3558_ = lean_apply_2(v_exportEntriesFn_3550_, v_env_3524_, v___x_3557_);
v_exported_3559_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_exported_3559_);
lean_dec_ref(v___x_3558_);
v___x_3560_ = lean_array_push(v_importedEntries_3556_, v_exported_3559_);
v___x_3561_ = lean_unsigned_to_nat(0u);
v___x_3562_ = lean_array_get_size(v___x_3560_);
v___x_3563_ = lean_nat_dec_lt(v___x_3561_, v___x_3562_);
if (v___x_3563_ == 0)
{
lean_dec_ref(v___x_3560_);
v___y_3539_ = v___x_3552_;
goto v___jp_3538_;
}
else
{
uint8_t v___x_3564_; 
v___x_3564_ = lean_nat_dec_le(v___x_3562_, v___x_3562_);
if (v___x_3564_ == 0)
{
if (v___x_3563_ == 0)
{
lean_dec_ref(v___x_3560_);
v___y_3539_ = v___x_3552_;
goto v___jp_3538_;
}
else
{
size_t v___x_3565_; size_t v___x_3566_; lean_object* v___x_3567_; 
v___x_3565_ = ((size_t)0ULL);
v___x_3566_ = lean_usize_of_nat(v___x_3562_);
v___x_3567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3560_, v___x_3565_, v___x_3566_, v___x_3552_);
lean_dec_ref(v___x_3560_);
v___y_3539_ = v___x_3567_;
goto v___jp_3538_;
}
}
else
{
size_t v___x_3568_; size_t v___x_3569_; lean_object* v___x_3570_; 
v___x_3568_ = ((size_t)0ULL);
v___x_3569_ = lean_usize_of_nat(v___x_3562_);
v___x_3570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3560_, v___x_3568_, v___x_3569_, v___x_3552_);
lean_dec_ref(v___x_3560_);
v___y_3539_ = v___x_3570_;
goto v___jp_3538_;
}
}
v___jp_3538_:
{
lean_object* v_tables_3540_; lean_object* v_leadingTable_3541_; lean_object* v_trailingTable_3542_; lean_object* v_firstTokens_3543_; lean_object* v_firstTokens_3544_; lean_object* v___x_3546_; 
v_tables_3540_ = lean_ctor_get(v_val_3534_, 2);
v_leadingTable_3541_ = lean_ctor_get(v_tables_3540_, 0);
v_trailingTable_3542_ = lean_ctor_get(v_tables_3540_, 2);
lean_inc(v_trailingTable_3542_);
lean_inc(v_leadingTable_3541_);
lean_inc(v_val_3534_);
v_firstTokens_3543_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3534_, v_leadingTable_3541_, v___y_3539_);
v_firstTokens_3544_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3534_, v_trailingTable_3542_, v_firstTokens_3543_);
if (v_isShared_3537_ == 0)
{
lean_ctor_set_tag(v___x_3536_, 0);
lean_ctor_set(v___x_3536_, 0, v_firstTokens_3544_);
v___x_3546_ = v___x_3536_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_firstTokens_3544_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
else
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
lean_dec(v___x_3533_);
lean_dec_ref(v_env_3524_);
v___x_3572_ = lean_box(1);
v___x_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3572_);
return v___x_3573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_3574_);
lean_dec(v___y_3574_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t v_includeUnnamed_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_){
_start:
{
lean_object* v___x_3585_; lean_object* v_env_3586_; lean_object* v___x_3587_; lean_object* v_toEnvExtension_3588_; lean_object* v_exportEntriesFn_3589_; lean_object* v_asyncMode_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v_importedEntries_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v_exported_3598_; lean_object* v___x_3599_; size_t v_sz_3600_; size_t v___x_3601_; lean_object* v___x_3602_; 
v___x_3585_ = lean_st_ref_get(v_a_3583_);
v_env_3586_ = lean_ctor_get(v___x_3585_, 0);
lean_inc_ref_n(v_env_3586_, 4);
lean_dec(v___x_3585_);
v___x_3587_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_3588_ = lean_ctor_get(v___x_3587_, 0);
v_exportEntriesFn_3589_ = lean_ctor_get(v___x_3587_, 4);
v_asyncMode_3590_ = lean_ctor_get(v_toEnvExtension_3588_, 2);
v___x_3591_ = lean_box(1);
v___x_3592_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_3593_ = lean_box(0);
v___x_3594_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3592_, v_toEnvExtension_3588_, v_env_3586_, v_asyncMode_3590_, v___x_3593_);
v_importedEntries_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc_ref(v_importedEntries_3595_);
lean_dec(v___x_3594_);
v___x_3596_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3591_, v___x_3587_, v_env_3586_, v_asyncMode_3590_, v___x_3593_);
lean_inc_ref(v_exportEntriesFn_3589_);
v___x_3597_ = lean_apply_2(v_exportEntriesFn_3589_, v_env_3586_, v___x_3596_);
v_exported_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_exported_3598_);
lean_dec_ref(v___x_3597_);
v___x_3599_ = lean_array_push(v_importedEntries_3595_, v_exported_3598_);
v_sz_3600_ = lean_array_size(v___x_3599_);
v___x_3601_ = ((size_t)0ULL);
v___x_3602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v___x_3599_, v_sz_3600_, v___x_3601_, v___x_3591_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_);
lean_dec_ref(v___x_3599_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3627_; 
v_a_3603_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3605_ = v___x_3602_;
v_isShared_3606_ = v_isSharedCheck_3627_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3602_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3627_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3607_; lean_object* v_ext_3608_; lean_object* v_toEnvExtension_3609_; lean_object* v_asyncMode_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v_categories_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3607_ = l_Lean_Parser_parserExtension;
v_ext_3608_ = lean_ctor_get(v___x_3607_, 1);
v_toEnvExtension_3609_ = lean_ctor_get(v_ext_3608_, 0);
v_asyncMode_3610_ = lean_ctor_get(v_toEnvExtension_3609_, 2);
v___x_3611_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref(v_env_3586_);
v___x_3612_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3611_, v___x_3607_, v_env_3586_, v_asyncMode_3610_);
v_categories_3613_ = lean_ctor_get(v___x_3612_, 2);
lean_inc_ref(v_categories_3613_);
lean_dec(v___x_3612_);
v___x_3614_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0));
v___x_3615_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3616_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3613_, v___x_3615_);
lean_dec_ref(v_categories_3613_);
if (lean_obj_tag(v___x_3616_) == 1)
{
lean_object* v_val_3617_; lean_object* v___x_3618_; lean_object* v_a_3619_; lean_object* v_kinds_3620_; lean_object* v___x_3621_; lean_object* v___f_3622_; lean_object* v___x_3623_; 
lean_del_object(v___x_3605_);
v_val_3617_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_val_3617_);
lean_dec_ref_known(v___x_3616_, 1);
v___x_3618_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v_a_3583_);
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3619_);
lean_dec_ref(v___x_3618_);
v_kinds_3620_ = lean_ctor_get(v_val_3617_, 1);
lean_inc_ref(v_kinds_3620_);
lean_dec(v_val_3617_);
v___x_3621_ = lean_box(v_includeUnnamed_3579_);
v___f_3622_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed), 12, 5);
lean_closure_set(v___f_3622_, 0, v_env_3586_);
lean_closure_set(v___f_3622_, 1, v___x_3593_);
lean_closure_set(v___f_3622_, 2, v_a_3603_);
lean_closure_set(v___f_3622_, 3, v_a_3619_);
lean_closure_set(v___f_3622_, 4, v___x_3621_);
v___x_3623_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_kinds_3620_, v___x_3614_, v___f_3622_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_);
lean_dec_ref(v_kinds_3620_);
return v___x_3623_;
}
else
{
lean_object* v___x_3625_; 
lean_dec(v___x_3616_);
lean_dec(v_a_3603_);
lean_dec_ref(v_env_3586_);
if (v_isShared_3606_ == 0)
{
lean_ctor_set(v___x_3605_, 0, v___x_3614_);
v___x_3625_ = v___x_3605_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3614_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
lean_dec_ref(v_env_3586_);
v_a_3628_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___x_3602_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3602_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
if (v_isShared_3631_ == 0)
{
v___x_3633_ = v___x_3630_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3628_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object* v_includeUnnamed_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_){
_start:
{
uint8_t v_includeUnnamed_boxed_3642_; lean_object* v_res_3643_; 
v_includeUnnamed_boxed_3642_ = lean_unbox(v_includeUnnamed_3636_);
v_res_3643_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v_includeUnnamed_boxed_3642_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_);
lean_dec(v_a_3640_);
lean_dec_ref(v_a_3639_);
lean_dec(v_a_3638_);
lean_dec_ref(v_a_3637_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object* v_as_3644_, size_t v_sz_3645_, size_t v_i_3646_, lean_object* v_b_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v___x_3653_; 
v___x_3653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_3644_, v_sz_3645_, v_i_3646_, v_b_3647_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object* v_as_3654_, lean_object* v_sz_3655_, lean_object* v_i_3656_, lean_object* v_b_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
size_t v_sz_boxed_3663_; size_t v_i_boxed_3664_; lean_object* v_res_3665_; 
v_sz_boxed_3663_ = lean_unbox_usize(v_sz_3655_);
lean_dec(v_sz_3655_);
v_i_boxed_3664_ = lean_unbox_usize(v_i_3656_);
lean_dec(v_i_3656_);
v_res_3665_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(v_as_3654_, v_sz_boxed_3663_, v_i_boxed_3664_, v_b_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
lean_dec(v___y_3661_);
lean_dec_ref(v___y_3660_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
lean_dec_ref(v_as_3654_);
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
lean_object* v___x_3671_; 
v___x_3671_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_3669_);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
lean_object* v_res_3677_; 
v_res_3677_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_);
lean_dec(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec(v___y_3673_);
lean_dec_ref(v___y_3672_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object* v_00_u03c3_3678_, lean_object* v_00_u03b2_3679_, lean_object* v_map_3680_, lean_object* v_init_3681_, lean_object* v_f_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
_start:
{
lean_object* v___x_3688_; 
v___x_3688_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_3680_, v_init_3681_, v_f_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object* v_00_u03c3_3689_, lean_object* v_00_u03b2_3690_, lean_object* v_map_3691_, lean_object* v_init_3692_, lean_object* v_f_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v_res_3699_; 
v_res_3699_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(v_00_u03c3_3689_, v_00_u03b2_3690_, v_map_3691_, v_init_3692_, v_f_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v_map_3691_);
return v_res_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object* v_map_3700_, lean_object* v_f_3701_, lean_object* v_init_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
lean_object* v___x_3708_; 
v___x_3708_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3701_, v_map_3700_, v_init_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object* v_map_3709_, lean_object* v_f_3710_, lean_object* v_init_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v_res_3717_; 
v_res_3717_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(v_map_3709_, v_f_3710_, v_init_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
return v_res_3717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object* v_00_u03c3_3718_, lean_object* v_00_u03c3_3719_, lean_object* v_00_u03b2_3720_, lean_object* v_map_3721_, lean_object* v_f_3722_, lean_object* v_init_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
lean_object* v___x_3729_; 
v___x_3729_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3722_, v_map_3721_, v_init_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object* v_00_u03c3_3730_, lean_object* v_00_u03c3_3731_, lean_object* v_00_u03b2_3732_, lean_object* v_map_3733_, lean_object* v_f_3734_, lean_object* v_init_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(v_00_u03c3_3730_, v_00_u03c3_3731_, v_00_u03b2_3732_, v_map_3733_, v_f_3734_, v_init_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object* v_00_u03c3_3742_, lean_object* v_00_u03c3_3743_, lean_object* v_00_u03b1_3744_, lean_object* v_00_u03b2_3745_, lean_object* v_f_3746_, lean_object* v_x_3747_, lean_object* v_x_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3746_, v_x_3747_, v_x_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03c3_3755_, lean_object* v_00_u03c3_3756_, lean_object* v_00_u03b1_3757_, lean_object* v_00_u03b2_3758_, lean_object* v_f_3759_, lean_object* v_x_3760_, lean_object* v_x_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(v_00_u03c3_3755_, v_00_u03c3_3756_, v_00_u03b1_3757_, v_00_u03b2_3758_, v_f_3759_, v_x_3760_, v_x_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_3768_, lean_object* v_00_u03b2_3769_, lean_object* v_00_u03c3_3770_, lean_object* v_00_u03c3_3771_, lean_object* v_f_3772_, lean_object* v_as_3773_, size_t v_i_3774_, size_t v_stop_3775_, lean_object* v_b_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
lean_object* v___x_3782_; 
v___x_3782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3772_, v_as_3773_, v_i_3774_, v_stop_3775_, v_b_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_3783_, lean_object* v_00_u03b2_3784_, lean_object* v_00_u03c3_3785_, lean_object* v_00_u03c3_3786_, lean_object* v_f_3787_, lean_object* v_as_3788_, lean_object* v_i_3789_, lean_object* v_stop_3790_, lean_object* v_b_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
size_t v_i_boxed_3797_; size_t v_stop_boxed_3798_; lean_object* v_res_3799_; 
v_i_boxed_3797_ = lean_unbox_usize(v_i_3789_);
lean_dec(v_i_3789_);
v_stop_boxed_3798_ = lean_unbox_usize(v_stop_3790_);
lean_dec(v_stop_3790_);
v_res_3799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_3783_, v_00_u03b2_3784_, v_00_u03c3_3785_, v_00_u03c3_3786_, v_f_3787_, v_as_3788_, v_i_boxed_3797_, v_stop_boxed_3798_, v_b_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec(v___y_3793_);
lean_dec_ref(v___y_3792_);
lean_dec_ref(v_as_3788_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object* v_00_u03c3_3800_, lean_object* v_00_u03c3_3801_, lean_object* v_00_u03b1_3802_, lean_object* v_00_u03b2_3803_, lean_object* v_f_3804_, lean_object* v_keys_3805_, lean_object* v_vals_3806_, lean_object* v_heq_3807_, lean_object* v_i_3808_, lean_object* v_acc_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_){
_start:
{
lean_object* v___x_3815_; 
v___x_3815_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3804_, v_keys_3805_, v_vals_3806_, v_i_3808_, v_acc_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_);
return v___x_3815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03c3_3816_, lean_object* v_00_u03c3_3817_, lean_object* v_00_u03b1_3818_, lean_object* v_00_u03b2_3819_, lean_object* v_f_3820_, lean_object* v_keys_3821_, lean_object* v_vals_3822_, lean_object* v_heq_3823_, lean_object* v_i_3824_, lean_object* v_acc_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(v_00_u03c3_3816_, v_00_u03c3_3817_, v_00_u03b1_3818_, v_00_u03b2_3819_, v_f_3820_, v_keys_3821_, v_vals_3822_, v_heq_3823_, v_i_3824_, v_acc_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
lean_dec_ref(v_vals_3822_);
lean_dec_ref(v_keys_3821_);
return v_res_3831_;
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
